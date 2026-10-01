// Generator records deliberately use their own collections and never Sudoku boards.
import {createHash} from 'node:crypto';
import {fail,unpack} from '../group-sudoku-records/cloudflare/worker.mjs';
import {groups} from '../../courses/abstract-algebra/generators/model.mjs';
import {levels,closure,minimumGenerators} from '../../courses/abstract-algebra/generators/challenge-model.mjs';
const keys=['C4','V4','S3','D4','Q8','S4','F56','A5','S5'];
export function verifyAttempt(input){
 if(Array.isArray(input.stages)){const g=groups[input.key];if(!g||input.stages.length!==levels(g).length)throw fail(400,'需要完整大关的通关记录。');const stages=input.stages.map((a,i)=>{if(a.key!==input.key||a.stage!==i)throw fail(400,'小关顺序不正确。');return verifyAttempt({...a,stages:undefined,submissionId:input.submissionId});});if(stages.some(a=>!a.won))throw fail(400,'大关尚未完成。');return {...stages.at(-1),stages,won:true};}

 const {key,stage,seeds,preset=null,seconds}=input,g=keys.includes(key)&&groups[key];
 if(!g||!Number.isInteger(stage)||!levels(g)[stage]||!Array.isArray(seeds)||!seeds.length||seeds.length>levels(g)[stage].budget||new Set(seeds).size!==seeds.length||seeds.some(x=>!Number.isInteger(x)||x<0||x>=g.table.length||x===g.e)||!Number.isInteger(seconds)||seconds<0||seconds>86400)throw fail(400,'生成记录格式不正确。');
 if(levels(g)[stage].preset&&(!seeds.includes(preset)||!minimumGenerators(g).eligible.includes(preset)))throw fail(400,'预设生成元不正确。');
 if(!/^[a-f0-9]{8}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{12}$/i.test(input.submissionId||''))throw fail(400,'缺少提交编号。');
 return {key,stage,seeds,preset,seconds,won:closure(g,seeds).size===g.table.length};
}
function completedRow(source){if(!source)return source;const row=JSON.parse(JSON.stringify(source));row.journey ||= {};for(const k of keys)if((row.journey[k]?.passed||0)<levels(groups[k]).length)delete row.journey[k];row.highest=Math.max(...keys.map((k,i)=>row.journey[k]?.passed?i:-1));row.completedLevels=keys.reduce((n,k)=>n+(row.journey[k]?.passed||0),0);return row;}
const one=r=>Array.isArray(r.data)?r.data[0]:r.data;
export function createGeneratorStore(db,prefix='generators_'){
 const col=(n,tx=db)=>tx.collection(prefix+n);
 return {
  async record(id){return completedRow(one(await col('records').doc(id).get()));},
  async records(){const rows=[];for(let n=0;;n+=100){const batch=(await col('records').orderBy('_id','asc').skip(n).limit(100).get()).data;rows.push(...batch.map(completedRow));if(batch.length<100)return rows;}},
  async sync(account,input,at){return db.runTransaction(async tx=>{
   const ref=col('records',tx).doc(account.id),old=completedRow(one(await ref.get()));
   if((input.epoch||0)!==(old?.epoch||0))return {...old,reset:true};
   const row=old?Object.fromEntries(Object.entries(old).filter(([k])=>k!=='_id')):{...account,journey:{},consumedLives:0,highest:-1,completedLevels:0,reachedAt:null,epoch:0};
   let advanced=false;
   for(const key of keys){const local=input.journey?.[key];if(!local)continue;const count=levels(groups[key]).length;
    if(!Number.isInteger(local.passed)||local.passed<0||local.passed>count)throw fail(400,'通关进度格式不正确。');
    if(local.passed===count&&local.passed>(row.journey[key]?.passed||0)){row.journey[key]={version:2,passed:local.passed,cleared:Array.from({length:local.passed},()=>true),times:Array.from({length:local.passed},(_,i)=>Number.isInteger(local.times?.[i])&&local.times[i]>=0&&local.times[i]<=86400?local.times[i]:null)};advanced=true;}
   }
   if(advanced){row.consumedLives=Math.max(row.consumedLives||0,Number.isSafeInteger(input.consumedLives)&&input.consumedLives>=0?input.consumedLives:0);row.highest=Math.max(...keys.map((k,i)=>row.journey[k]?.passed?i:-1));row.completedLevels=keys.reduce((n,k)=>n+(row.journey[k]?.passed||0),0);row.reachedAt=at;row.updatedAt=at;await ref.set(row);}
   return row;
  });},
  async reset(account,epoch,at){return db.runTransaction(async tx=>{
   const ref=col('records',tx).doc(account.id),old=completedRow(one(await ref.get()));
   if(epoch!==(old?.epoch||0))throw fail(409,'记录已更新，请刷新后重试。');
   const row={...account,journey:{},consumedLives:0,highest:-1,completedLevels:0,reachedAt:null,epoch:epoch+1,updatedAt:at};await ref.set(row);return row;
  });},
  async save(account,input,attempt,at){return db.runTransaction(async tx=>{
   const request=col('requests',tx).doc(input.submissionId),ref=col('records',tx).doc(account.id),prior=one(await request.get()),old=completedRow(one(await ref.get()));
   if((input.epoch||0)!==(old?.epoch||0))throw fail(409,'记录已清除，请重新同步。');
   const fingerprint=createHash('sha256').update(JSON.stringify(attempt)).digest('hex');
   if(prior){if(prior.accountId!==account.id||prior.fingerprint!==fingerprint)throw fail(409,'提交编号已使用。');return old;}
   if((old?.journey?.[attempt.key]?.passed||0)>attempt.stage)return old;
   const row=old?Object.fromEntries(Object.entries(old).filter(([key])=>key!=="_id")):{...account,journey:{},consumedLives:0,highest:-1,completedLevels:0,reachedAt:null};
   const minute=Math.floor(Date.parse(at)/60000);row.rateCount=row.rateMinute===minute?(row.rateCount||0)+1:1;row.rateMinute=minute;if(row.rateCount>60)throw fail(429,'同步过于频繁，请稍后重试。');
   const r=row.journey[attempt.key]||{version:2,passed:0,times:[]};
   r.cleared ||= Array.from({length:r.passed},()=>true);
   if(attempt.won&&(attempt.stages||levels(groups[attempt.key]).length===1)){const count=levels(groups[attempt.key]).length;r.passed=count;r.cleared=Array.from({length:count},()=>true);r.times=(attempt.stages||[attempt]).map(a=>a.seconds);row.completedLevels+=count;row.highest=Math.max(row.highest,keys.indexOf(attempt.key));row.reachedAt=at;}

   if(!attempt.won)row.consumedLives++;
   if(r.passed===levels(groups[attempt.key]).length)row.journey[attempt.key]=r;row.updatedAt=at;
   await request.set({accountId:account.id,fingerprint,createdAt:at});await ref.set(row);return row;
  });}
 };
}
export function generatorPublic(r,full=false){return {kind:r.kind,name:r.kind==='guest'?'游客 '+r.name:full?r.name:r.initials||'—',studentId:r.kind==='guest'?'':full?r.id:r.id.slice(0,3)+'****'+r.id.slice(-4),highest:r.highest,completedLevels:r.completedLevels,consumedLives:r.consumedLives,reachedAt:r.reachedAt};}
export async function handleGenerators(event,{generatorStore:store,secret},now){
 if(!store)throw fail(503,'生成元服务尚未配置。');
 const {path,method='GET',token,body={}}=event;
 if(method==='GET'&&(path==='/api/generators/records'||path==='/api/generators/admin/records')){
  const full=path.includes('/admin/');if(full&&!await unpack(token,'admin',secret,now))throw fail(401,'请先进行教师登录。');
  const rows=(await store.records()).filter(r=>r.highest>=0).sort((a,b)=>b.highest-a.highest||String(a.reachedAt||'9999').localeCompare(String(b.reachedAt||'9999')));
  return {status:200,data:{records:rows.map(r=>generatorPublic(r,full)),total:rows.length}};
 }
 const session=await unpack(token,'player',secret,now);if(!session)throw fail(401,'登录已过期，请重新登录，进度已保留在本机。');
 if(path==='/api/generators/progress'&&method==='GET'){const r=await store.record(session.account.id);return {status:200,data:{journey:r?.journey||{},consumedLives:r?.consumedLives||0,epoch:r?.epoch||0}};}
 if(path==='/api/generators/sync'&&method==='POST'){const r=await store.sync(session.account,body,new Date(now).toISOString());return {status:200,data:{journey:r.journey,consumedLives:r.consumedLives,epoch:r.epoch||0,reset:!!r.reset}};}
 if(path==='/api/generators/reset'&&method==='POST'){if(body.confirm!==true||!Number.isSafeInteger(body.epoch))throw fail(400,'请确认清除本账号记录。');const r=await store.reset(session.account,body.epoch,new Date(now).toISOString());return {status:200,data:{journey:{},consumedLives:0,epoch:r.epoch,reset:true}};}
 if(path==='/api/generators/attempts'&&method==='POST'){const attempt=verifyAttempt(body),r=await store.save(session.account,body,attempt,new Date(now).toISOString());return {status:200,data:{saved:true,journey:r.journey,consumedLives:r.consumedLives,record:generatorPublic(r)}};}
 throw fail(404,'未找到此接口。');
}
