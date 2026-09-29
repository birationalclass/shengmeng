// Generator records deliberately use their own collections and never Sudoku boards.
import {createHash} from 'node:crypto';
import {fail,unpack} from '../group-sudoku-records/cloudflare/worker.mjs';
import {groups} from '../../courses/abstract-algebra/generators/model.mjs';
import {levels,closure,minimumGenerators} from '../../courses/abstract-algebra/generators/challenge-model.mjs';
const keys=['C4','V4','S3','D4','Q8','S4','F56','A5','S5'];
export function verifyAttempt(input){
 const {key,stage,seeds,preset=null,seconds}=input,g=keys.includes(key)&&groups[key];
 if(!g||!Number.isInteger(stage)||!levels(g)[stage]||!Array.isArray(seeds)||!seeds.length||seeds.length>levels(g)[stage].budget||new Set(seeds).size!==seeds.length||seeds.some(x=>!Number.isInteger(x)||x<0||x>=g.table.length||x===g.e)||!Number.isInteger(seconds)||seconds<0||seconds>86400)throw fail(400,'生成记录格式不正确。');
 if(levels(g)[stage].preset&&(!seeds.includes(preset)||!minimumGenerators(g).eligible.includes(preset)))throw fail(400,'预设生成元不正确。');
 if(!/^[a-f0-9]{8}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{12}$/i.test(input.submissionId||''))throw fail(400,'缺少提交编号。');
 return {key,stage,seeds,preset,seconds,won:closure(g,seeds).size===g.table.length};
}
const one=r=>Array.isArray(r.data)?r.data[0]:r.data;
export function createGeneratorStore(db,prefix='generators_'){
 const col=(n,tx=db)=>tx.collection(prefix+n);
 return {
  async record(id){return one(await col('records').doc(id).get());},
  async records(){const rows=[];for(let n=0;;n+=100){const batch=(await col('records').orderBy('_id','asc').skip(n).limit(100).get()).data;rows.push(...batch);if(batch.length<100)return rows;}},
  async save(account,input,attempt,at){return db.runTransaction(async tx=>{
   const request=col('requests',tx).doc(input.submissionId),ref=col('records',tx).doc(account.id),prior=one(await request.get()),old=one(await ref.get());
   const fingerprint=createHash('sha256').update(JSON.stringify(attempt)).digest('hex');
   if(prior){if(prior.accountId!==account.id||prior.fingerprint!==fingerprint)throw fail(409,'提交编号已使用。');return old;}
   const row=old?Object.fromEntries(Object.entries(old).filter(([key])=>key!=="_id")):{...account,journey:{},consumedLives:0,highest:-1,completedLevels:0,reachedAt:null};
   const minute=Math.floor(Date.parse(at)/60000);row.rateCount=row.rateMinute===minute?(row.rateCount||0)+1:1;row.rateMinute=minute;if(row.rateCount>60)throw fail(429,'同步过于频繁，请稍后重试。');
   const r=row.journey[attempt.key]||{version:2,passed:0,times:[]};
   r.cleared ||= Array.from({length:r.passed},()=>true);
   if(attempt.won&&!r.cleared[attempt.stage]){r.cleared[attempt.stage]=true;r.times[attempt.stage]=attempt.seconds;const before=r.passed;while(r.cleared[r.passed])r.passed++;row.completedLevels+=r.passed-before;if(r.passed>before){row.highest=Math.max(row.highest,keys.indexOf(attempt.key));row.reachedAt=at;}}
   if(!attempt.won)row.consumedLives++;
   row.journey[attempt.key]=r;row.updatedAt=at;
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
  const rows=(await store.records()).sort((a,b)=>b.highest-a.highest||String(a.reachedAt||'9999').localeCompare(String(b.reachedAt||'9999')));
  return {status:200,data:{records:rows.map(r=>generatorPublic(r,full)),total:rows.length}};
 }
 const session=await unpack(token,'player',secret,now);if(!session)throw fail(401,'登录已过期，请重新登录，进度已保留在本机。');
 if(path==='/api/generators/progress'&&method==='GET'){const r=await store.record(session.account.id);return {status:200,data:{journey:r?.journey||{},consumedLives:r?.consumedLives||0}};}
 if(path==='/api/generators/attempts'&&method==='POST'){const attempt=verifyAttempt(body),r=await store.save(session.account,body,attempt,new Date(now).toISOString());return {status:200,data:{saved:true,journey:r.journey,consumedLives:r.consumedLives,record:generatorPublic(r)}};}
 throw fail(404,'未找到此接口。');
}
