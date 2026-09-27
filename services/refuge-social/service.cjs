const {randomBytes,createHash,scrypt:derive,timingSafeEqual}=require('node:crypto');
const {promisify}=require('node:util');
const scrypt=promisify(derive),hash=s=>createHash('sha256').update(s).digest('hex');
const fault=(status,message)=>Object.assign(new Error(message),{status});
const publicUser=u=>({id:u.id,name:u.name,role:u.role==='admin'?'admin':'member',mutedUntil:u.mutedUntil||0});
const passwordHash=async(password,salt)=>Buffer.from(await scrypt(password,salt,64)).toString('hex');
const COOKIE='refuge_session';
function createHandler(store,{origins=['https://birationalclass.github.io'],secure=true,now=Date.now,cookieName=COOKIE,ai=null}={}){
 return async function handle(event){
  const h=Object.fromEntries(Object.entries(event.headers||{}).map(([k,v])=>[k.toLowerCase(),v]));
  const headers={'Content-Type':'application/json; charset=utf-8','Cache-Control':'no-store','X-Content-Type-Options':'nosniff','Vary':'Origin'};
  const send=(status,data)=>({statusCode:status,headers,body:status===204?'':JSON.stringify(data),isBase64Encoded:false});
  const at=now(),ip=event.trustedIp||'gateway';
  const cookie=(token,age)=>{headers['Set-Cookie']=`${cookieName}=${token}; Path=/; HttpOnly; ${secure?'Secure; SameSite=None; Partitioned':'SameSite=Lax'}${age===null?'':`; Max-Age=${age}`}`;};
  async function rate(scope,max,period=60000){const slot=Math.floor(at/period);if(await store.rate(hash(scope+':'+slot),at+period*2)>max)throw fault(429,'稍等片刻再试');}
  async function account(){
   const token=(h.cookie||'').split(';').map(v=>v.trim()).find(v=>v.startsWith(cookieName+'='))?.slice(cookieName.length+1);
   if(!/^[a-f0-9]{64}$/.test(token||''))throw fault(401,'请先登录');
   const session=await store.get('sessions',hash(token));if(!session||session.expiresAt<=at)throw fault(401,'请重新登录');
   const user=await store.get('users',session.userId);if(!user)throw fault(401,'请重新登录');
   return {user,sessionId:hash(token)};
  }
  async function session(user,remember){await store.update('users',user.id,{lastLoginAt:at});const token=randomBytes(32).toString('hex'),age=remember?30*86400:86400;await store.put('sessions',hash(token),{userId:user.id,expiresAt:at+age*1000});cookie(token,remember?age:null);return publicUser(user);}
  try{
   if(h.origin&&!origins.includes(h.origin))throw fault(403,'来源不允许');
   if(h.origin){headers['Access-Control-Allow-Origin']=h.origin;headers['Access-Control-Allow-Credentials']='true';}
   if(event.httpMethod==='OPTIONS'){headers['Access-Control-Allow-Methods']='GET,POST,OPTIONS';headers['Access-Control-Allow-Headers']='Content-Type';return send(204);}
   const path=event.path.replace(/^\/refuge(?:-test)?(?=\/|$)/,''),method=event.httpMethod;
   if(path==='/api/health'&&method==='GET')return send(200,{ready:true,service:'refuge-social'});
   let input={};
   if(method==='POST'){
    if(!h.origin||!origins.includes(h.origin))throw fault(403,'来源不允许');
    if(!/^application\/json\b/.test(h['content-type']||''))throw fault(415,'请求格式不正确');
    const raw=event.isBase64Encoded?Buffer.from(event.body||'','base64').toString():event.body||'';
    if(Buffer.byteLength(raw)>(path==='/api/ai/start'?650000:4096))throw fault(413,'内容过长');
    try{input=JSON.parse(raw);}catch{throw fault(400,'请求格式不正确');}
    if(!input||Array.isArray(input)||typeof input!=='object')throw fault(400,'请求格式不正确');
   }
   if(['/api/register','/api/login'].includes(path)&&method==='POST'){
    await rate('auth-ip:'+ip,20);
    const name=typeof input.name==='string'?input.name.normalize('NFKC').trim():'',password=input.password;
    if(!/^[\p{L}\p{N}_-]{3,24}$/u.test(name)||typeof password!=='string'||password.length<(path==='/api/register'?8:1)||password.length>128)throw fault(400,'账号需 3–24 字，密码至少 8 位');
    const id=hash(name.toLocaleLowerCase('en-US'));await rate('auth-name:'+id,10);
    let user=await store.get('users',id);
    if(path==='/api/register'){
     await rate('register:'+ip,5,3600000);if(user)throw fault(409,'这个名字已被使用');
     const salt=randomBytes(16).toString('hex');user={id,name,salt,password:await passwordHash(password,salt),createdAt:at,role:'member'};
     if(!await store.create('users',id,user))throw fault(409,'这个名字已被使用');
    }else{
     const derived=await passwordHash(password,user?.salt||'refuge-unknown-account-salt');
     if(!user||!timingSafeEqual(Buffer.from(derived,'hex'),Buffer.from(user.password,'hex')))throw fault(401,'账号或密码不正确');
    }
    return send(200,{user:await session(user,input.remember!==false)});
   }
   if(path==='/api/session'&&method==='GET'){const {user}=await account();return send(200,{user:publicUser(user)});}
   if(path==='/api/logout'&&method==='POST'){const {sessionId}=await account();await store.remove('sessions',sessionId);cookie('',0);return send(200,{ok:true});}
   if(path.startsWith('/api/ai/')){
    const {user}=await account();if(!ai)throw fault(503,'AI 尚未配置');
    const publicJob=job=>({id:job.id,status:job.status,text:job.text||'',question:job.question,provider:job.provider,createdAt:job.createdAt,updatedAt:job.updatedAt,error:job.error||null});
    if(path==='/api/ai/providers'&&method==='GET')return send(200,{providers:await ai.list()});
    if(path==='/api/ai/history'&&method==='GET'){await rate('ai-history:'+user.id,15);return send(200,{jobs:(await store.aiHistory(user.id)).reverse().map(publicJob)});}
    if(path==='/api/ai/start'&&method==='POST'){
     if(user.mutedUntil>at)throw fault(403,'禁言期间不可调用 AI');
     if(!/^[a-f0-9-]{36}$/i.test(input.id||''))throw fault(400,'任务编号无效');
     if(!['openai','qwen'].includes(input.provider))throw fault(400,'不支持的 AI 服务');
     if(typeof input.image!=='string'||!/^data:image\/jpeg;base64,[A-Za-z0-9+/]+=*$/.test(input.image))throw fault(400,'请提供场景截图');
     const bytes=Buffer.from(input.image.split(',')[1],'base64');if(bytes.length>450000||bytes.length<4||bytes[0]!==255||bytes[1]!==216||bytes[2]!==255)throw fault(400,'截图格式或大小不正确');
     const id=hash(user.id+':ai:'+input.id),existing=await store.get('ai_jobs',id);if(existing)return send(200,{job:publicJob(existing)});
     await rate('ai:'+user.id,3);await rate('ai-day:'+user.id,20,86400000);await rate('ai-total',100,86400000);
     const question=typeof input.question==='string'?input.question.trim().slice(0,1500):'请解释当前画面，优先讲解其中可见的数学内容。';
     const job={id,userId:user.id,provider:input.provider,question:question||'请解释当前画面。',createdAt:at,updatedAt:at,status:'starting'};
     if(!await store.create('ai_jobs',id,job))return send(200,{job:publicJob(await store.get('ai_jobs',id))});
     try{const result=await ai.start({...input,question:job.question});Object.assign(job,result,{updatedAt:now()});if(!job.responseId&&job.status!=='completed')throw fault(503,'AI 未返回任务编号');await store.put('ai_jobs',id,job);}catch(e){await store.update('ai_jobs',id,{status:'failed',error:e.status?e.message:'AI 请求失败',updatedAt:now()});throw e;}
     return send(200,{job:publicJob(job)});
    }
    if(path==='/api/ai/poll'&&method==='POST'){
     if(!/^[a-f0-9]{64}$/.test(input.id||''))throw fault(400,'任务无效');const job=await store.get('ai_jobs',input.id);if(!job||job.userId!==user.id)throw fault(404,'任务不存在');
     if(!['completed','failed','cancelled','incomplete'].includes(job.status)){
      await rate('ai-poll:'+user.id,20);if(now()-job.createdAt>600000){job.status='failed';job.error='任务已超时，请重新请求';}else if(job.responseId){Object.assign(job,await ai.poll(job));}job.updatedAt=now();await store.put('ai_jobs',job.id,job);
     }return send(200,{job:publicJob(job)});
    }
    throw fault(404,'接口不存在');
   }
   if(path.startsWith('/api/admin/')){
    const {user}=await account();if(user.role!=='admin')throw fault(403,'需要管理员权限');
    await rate('admin:'+user.id,30);
    if(path==='/api/admin/ai'&&method==='POST'){if(!ai)throw fault(503,'AI 尚未启用');await ai.save(input);return send(200,{ok:true});}
    if(path==='/api/admin/users'&&method==='POST'){
     const after=typeof input.after==='string'&&/^[a-f0-9]{64}$/.test(input.after)?input.after:'';
     const rows=await store.users(after),more=rows.length>50,list=rows.slice(0,50);
     return send(200,{users:list.map(u=>({...publicUser(u),createdAt:u.createdAt,lastLoginAt:u.lastLoginAt||null})),next:more?list.at(-1).id:null});
    }
    if(path==='/api/admin/mute'&&method==='POST'){
     if(![0,3600,86400,604800].includes(input.seconds))throw fault(400,'请选择禁言时长');
     if(!/^[a-f0-9]{64}$/.test(input.userId||''))throw fault(400,'账号无效');
     const target=await store.get('users',input.userId);if(!target)throw fault(404,'账号不存在');
     if(target.role==='admin')throw fault(400,'管理员账号不可禁言');
     const mutedUntil=input.seconds?at+input.seconds*1000:0;
     await store.update('users',target.id,{mutedUntil,moderatedBy:user.id,moderatedAt:at});
     return send(200,{user:{...publicUser(target),mutedUntil}});
    }
    throw fault(404,'接口不存在');
   }
   if(path==='/api/messages'&&method==='GET'){

    const {user}=await account();await rate('read:'+user.id,35);
    const messages=(await store.messages()).reverse().map(({id,name,text,createdAt,userId})=>({id,name,text,createdAt,mine:userId===user.id}));
    return send(200,{messages});
   }
   if(path==='/api/messages'&&method==='POST'){
    const {user}=await account();if(user.mutedUntil>at)throw fault(403,'禁言中，至 '+new Date(user.mutedUntil).toLocaleString('zh-CN',{timeZone:'Asia/Shanghai'}));await rate('chat:'+user.id,12);
    const text=typeof input.text==='string'?input.text.trim().replace(/[\u0000-\u0008\u000b-\u001f\u007f]/g,''):'';
    if(!text||[...text].length>300)throw fault(400,'消息请控制在 300 字以内');
    if(!/^[a-f0-9-]{36}$/i.test(input.id||''))throw fault(400,'消息编号无效');
    const id=hash(user.id+input.id),message={id,userId:user.id,name:user.name,text,createdAt:at};
    await store.create('messages',id,message);const saved=await store.get('messages',id);
    return send(200,{message:{id:saved.id,name:saved.name,text:saved.text,createdAt:saved.createdAt,mine:true}});
   }
   throw fault(404,'接口不存在');
  }catch(e){if(!e.status)console.error('[Refuge service]',e.message);return send(e.status||503,{error:e.status?e.message:'连接暂不可用'});}
 };
}
module.exports={createHandler};
