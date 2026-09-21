import clues from './clues.mjs';

const fail=(status,message)=>Object.assign(new Error(message),{status});
const encoder=new TextEncoder();
const b64=bytes=>btoa(String.fromCharCode(...bytes)).replaceAll('+','-').replaceAll('/','_').replace(/=+$/,'');
const unb64=s=>Uint8Array.from(atob(s.replaceAll('-','+').replaceAll('_','/')),c=>c.charCodeAt(0));
const keyFor=secret=>crypto.subtle.importKey('raw',encoder.encode(secret),{name:'HMAC',hash:'SHA-256'},false,['sign','verify']);
async function sign(value,secret){const body=b64(encoder.encode(JSON.stringify(value)));return body+'.'+b64(new Uint8Array(await crypto.subtle.sign('HMAC',await keyFor(secret),encoder.encode(body))));}
async function unpack(token,kind,secret,now){try{const parts=String(token).split('.');if(parts.length!==2)return null;const [body,sig]=parts;if(!await crypto.subtle.verify('HMAC',await keyFor(secret),unb64(sig),encoder.encode(body)))return null;const value=JSON.parse(new TextDecoder().decode(unb64(body)));return value.kind===kind&&value.exp>now?value:null;}catch{return null;}}
async function samePassword(a,b){const digest=async s=>new Uint8Array(await crypto.subtle.digest('SHA-256',encoder.encode(s)));const [x,y]=await Promise.all([digest(a),digest(b)]);let diff=0;for(let i=0;i<x.length;i++)diff|=x[i]^y[i];return diff===0;}

export function verifiedBoards(boards){
 if(!boards||typeof boards!=='object'||Array.isArray(boards))return false;
 for(let n=2;n<=9;n++){
  const v=boards[n];if(!Array.isArray(v)||v.length!==n*n||v.some((x,i)=>!Number.isInteger(x)||x<1||x>n||(clues[n][i]&&clues[n][i]!==x)))return false;
  for(let a=0;a<n;a++){
   if(new Set(v.slice(a*n,(a+1)*n)).size!==n||new Set(Array.from({length:n},(_,b)=>v[b*n+a])).size!==n)return false;
  }
  const at=(a,b)=>v[(a-1)*n+b-1];
  for(let a=1;a<=n;a++)for(let b=1;b<=n;b++)for(let c=1;c<=n;c++)if(at(at(a,b),c)!==at(a,at(b,c)))return false;
 }
 return true;
}
async function readBody(request){
 if(!/^application\/json\b/i.test(request.headers.get('Content-Type')||''))throw fail(415,'请使用 JSON 请求。');
 if(Number(request.headers.get('Content-Length'))>16384)throw fail(413,'提交内容过大。');
 const reader=request.body?.getReader();if(!reader)throw fail(400,'请求格式不正确。');let length=0,chunks=[];
 for(;;){const {done,value}=await reader.read();if(done)break;length+=value.length;if(length>16384){await reader.cancel();throw fail(413,'提交内容过大。');}chunks.push(value);}
 const bytes=new Uint8Array(length);let offset=0;for(const part of chunks){bytes.set(part,offset);offset+=part.length;}
 try{const value=JSON.parse(new TextDecoder().decode(bytes));if(!value||typeof value!=='object'||Array.isArray(value))throw Error();return value;}catch{throw fail(400,'请求格式不正确。');}
}
async function rate(env,ip,scope,max,now){
 // Persist sensitive-endpoint limits across Worker instances. IPs are keyed with a secret HMAC.
 const key=b64(new Uint8Array(await crypto.subtle.sign('HMAC',await keyFor(env.RECORDS_SECRET),encoder.encode(scope+':'+ip))));
 const minute=Math.floor(now/60000);
 const row=await env.DB.prepare('INSERT INTO rate_limits(key,minute,count) VALUES(?,?,1) ON CONFLICT(key) DO UPDATE SET minute=excluded.minute,count=CASE WHEN rate_limits.minute=excluded.minute THEN rate_limits.count+1 ELSE 1 END RETURNING count').bind(key,minute).first();
 if(row.count>max)throw fail(429,'操作过于频繁，请一分钟后再试。');
}
const mapRecord=(r,full=false)=>({studentId:full?r.id:r.id.slice(0,3)+'****'+r.id.slice(-4),name:full?r.name:r.initials,firstCompletedAt:r.first_at,updatedAt:r.updated_at,completedLevels:8});
const selectRecord='SELECT s.id,s.name,s.initials,c.first_at,c.updated_at FROM completions c JOIN students s ON s.id=c.student_id';
async function student(env,id){if(typeof id!=='string'||!/^\d{11}$/.test(id))throw fail(400,'请输入完整的 11 位学号。');const row=await env.DB.prepare('SELECT id,name FROM students WHERE id=?').bind(id).first();if(!row)throw fail(404,'点名册中没有这个学号，请核对后重试。');return row;}

export async function handle(request,env,now=Date.now()){
 const headers={'Content-Type':'application/json; charset=utf-8','Cache-Control':'no-store','X-Content-Type-Options':'nosniff','Vary':'Origin'};
 const send=(status,data)=>new Response(status===204?null:JSON.stringify(data),{status,headers});
 try{
  const origin=request.headers.get('Origin');const allowed=(env.RECORDS_ORIGINS||'https://birationalclass.github.io').split(',');
  if(origin&&!allowed.includes(origin))throw fail(403,'此来源不允许访问。');
  if(origin)headers['Access-Control-Allow-Origin']=origin;
  if(request.method==='OPTIONS'){headers['Access-Control-Allow-Methods']='GET,POST,OPTIONS';headers['Access-Control-Allow-Headers']='Content-Type,Authorization';return send(204);}
  if(!env.DB||!env.RECORDS_SECRET||env.RECORDS_SECRET.length<32||!env.RECORDS_ADMIN_PASSWORD||env.RECORDS_ADMIN_PASSWORD.length<16)throw fail(503,'通关登记服务尚未配置完成。');
  const path=new URL(request.url).pathname,ip=request.headers.get('CF-Connecting-IP')||'unknown';
  if(path==='/api/health'&&request.method==='GET'){const row=await env.DB.prepare('SELECT COUNT(*) AS total FROM students').first();return send(row.total?200:503,{ready:row.total>0,idLength:11});}
  if(path==='/api/lookup'&&request.method==='POST'){
   await rate(env,ip,'lookup',20,now);const input=await readBody(request),s=await student(env,input.studentId);
   return send(200,{name:s.name,lookupToken:await sign({kind:'lookup',id:s.id,exp:now+300000},env.RECORDS_SECRET)});
  }
  if(path==='/api/completions'&&request.method==='POST'){
   await rate(env,ip,'submit',12,now);const input=await readBody(request),s=await student(env,input.studentId),lookup=await unpack(input.lookupToken,'lookup',env.RECORDS_SECRET,now);
   if(!lookup||lookup.id!==s.id)throw fail(401,'姓名查询已过期，请重新输入学号。');
   if(input.name!==s.name)throw fail(400,'姓名与点名册不一致，请重新核对。');
   if(!/^[a-f0-9]{8}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{12}$/i.test(input.submissionId||''))throw fail(400,'缺少提交编号。');
   if(!verifiedBoards(input.boards))throw fail(400,'请先完成 2×2 至 9×9 全部关卡。');
   const old=await env.DB.prepare('SELECT student_id FROM requests WHERE id=?').bind(input.submissionId).first();
   if(old&&old.student_id!==s.id)throw fail(409,'提交编号已使用。');
   // Trigger updates completions only on first insertion. A retry cannot change its time.
   // A conflicting student ID violates NOT NULL, preventing a race from claiming another request.
   await env.DB.prepare('INSERT INTO requests(id,student_id,created_at,boards) VALUES(?,?,?,?) ON CONFLICT(id) DO UPDATE SET student_id=CASE WHEN requests.student_id=excluded.student_id THEN requests.student_id ELSE NULL END').bind(input.submissionId,s.id,new Date(now).toISOString(),JSON.stringify(input.boards)).run();
   const row=await env.DB.prepare(selectRecord+' WHERE s.id=?').bind(s.id).first();return send(200,{saved:true,record:mapRecord(row)});
  }
  if(path==='/api/records'&&request.method==='GET'){
   const {results}=await env.DB.prepare(selectRecord+' ORDER BY c.first_at ASC').all();return send(200,{records:results.map(r=>mapRecord(r)),total:results.length});
  }
  if(path==='/api/admin/session'&&request.method==='POST'){
   await rate(env,ip,'admin',5,now);const input=await readBody(request);if(typeof input.password!=='string'||!await samePassword(input.password,env.RECORDS_ADMIN_PASSWORD))throw fail(401,'教师口令不正确。');
   return send(200,{token:await sign({kind:'admin',exp:now+1800000},env.RECORDS_SECRET)});
  }
  if(path==='/api/admin/records'&&request.method==='GET'){
   if(!await unpack((request.headers.get('Authorization')||'').replace(/^Bearer /,''),'admin',env.RECORDS_SECRET,now))throw fail(401,'请先进行教师登录。');
   const {results}=await env.DB.prepare(selectRecord+' ORDER BY c.updated_at DESC').all();return send(200,{records:results.map(r=>mapRecord(r,true)),total:results.length});
  }
  throw fail(404,'未找到此接口。');
 }catch(e){return send(e.status||503,{error:e.status?e.message:'服务暂时不可用，请稍后重试。'});}
}
export default {
 fetch:(request,env)=>handle(request,env),
 async scheduled(controller,env){await env.DB.prepare('DELETE FROM rate_limits WHERE minute<?').bind(Math.floor(Date.now()/60000)-1440).run();}
};
