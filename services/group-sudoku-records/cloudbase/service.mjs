// CloudBase event-function protocol. The database is never exposed to browser clients.
import {createHmac} from 'node:crypto';
import {fail,sign,unpack,samePassword,mapRecord,verifiedBoards} from '../cloudflare/worker.mjs';

export async function handle(event,{store,secret,password,identity,adminIdentity=identity,lookupLimit=20},now=Date.now()){
 const send=(status,data)=>({status,data});
 try {
  if(!secret||secret.length<32||!password||password.length<8)throw fail(503,'通关登记服务尚未配置完成。');
  if(!identity)throw fail(401,'连接验证已失效，请刷新页面重试。');
  if(!event||typeof event!=='object'||Array.isArray(event))throw fail(400,'请求格式不正确。');
  if(Buffer.byteLength(JSON.stringify(event))>16384)throw fail(413,'提交内容过大。');
  const {path,method='GET',body:input={},token=''}=event;
  if(!input||typeof input!=='object'||Array.isArray(input))throw fail(400,'请求格式不正确。');
  const rate=async(scope,max)=>{
   const key=createHmac('sha256',secret).update(scope+':'+(scope==='admin'?adminIdentity:identity)).digest('hex');
   if(await store.rate(key,Math.floor(now/60000))>max)throw fail(429,'操作过于频繁，请一分钟后再试。');
  };
  const student=async id=>{
   if(typeof id!=='string'||!/^\d{11}$/.test(id))throw fail(400,'请输入完整的 11 位学号。');
   const s=await store.student(id);if(!s)throw fail(404,'点名册中没有这个学号，请核对后重试。');return s;
  };
  if(path==='/api/health'&&method==='GET'){
   const ready=await store.ready();return send(ready?200:503,{ready,idLength:11});
  }
  if(path==='/api/lookup'&&method==='POST'){
   await rate('lookup',lookupLimit);const s=await student(input.studentId);
   return send(200,{name:s.name,lookupToken:await sign({kind:'lookup',id:s.id,exp:now+300000},secret)});
  }
  if(path==='/api/completions'&&method==='POST'){
   await rate('submit',12);const s=await student(input.studentId),lookup=await unpack(input.lookupToken,'lookup',secret,now);
   if(!lookup||lookup.id!==s.id)throw fail(401,'姓名查询已过期，请重新输入学号。');
   if(input.name!==s.name)throw fail(400,'姓名与点名册不一致，请重新核对。');
   if(!/^[a-f0-9]{8}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{12}$/i.test(input.submissionId||''))throw fail(400,'缺少提交编号。');
   if(!verifiedBoards(input.boards))throw fail(400,'请先完成 2×2 至 9×9 全部关卡。');
   const record=await store.save(s,input,new Date(now).toISOString());return send(200,{saved:true,record:mapRecord(record)});
  }
  if(path==='/api/records'&&method==='GET'){
   const rows=await store.records();rows.sort((a,b)=>a.first_at.localeCompare(b.first_at));
   return send(200,{records:rows.map(r=>mapRecord(r)),total:rows.length});
  }
  if(path==='/api/admin/session'&&method==='POST'){
   await rate('admin',5);if(typeof input.password!=='string'||!await samePassword(input.password,password))throw fail(401,'教师口令不正确。');
   return send(200,{token:await sign({kind:'admin',exp:now+1800000},secret)});
  }
  if(path==='/api/admin/records'&&method==='GET'){
   if(!await unpack(token,'admin',secret,now))throw fail(401,'请先进行教师登录。');
   const rows=await store.records();rows.sort((a,b)=>b.updated_at.localeCompare(a.updated_at));
   return send(200,{records:rows.map(r=>mapRecord(r,true)),total:rows.length});
  }
  throw fail(404,'未找到此接口。');
 } catch(error) {
  if(!error.status)console.error('records service error',error.code||error.name);
  return send(error.status||503,{error:error.status?error.message:'服务暂时不可用，请稍后重试。'});
 }
}
