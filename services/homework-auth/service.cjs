const {randomBytes,randomInt,createHash,createHmac,scrypt:derive,timingSafeEqual}=require('node:crypto');
const {promisify}=require('node:util');
const scrypt=promisify(derive);
const hash=value=>createHash('sha256').update(value).digest('hex');
const fault=(status,message)=>Object.assign(new Error(message),{status});
const same=(a,b)=>typeof a==='string'&&typeof b==='string'&&a.length===b.length&&timingSafeEqual(Buffer.from(a),Buffer.from(b));
const publicUser=u=>({studentId:u.studentId,email:u.email,role:u.role});
const passwordHash=async(password,salt)=>Buffer.from(await scrypt(password,salt,64)).toString('hex');

// All mutable authentication decisions execute through store.transaction. Never
// accept an email address, role, user ID or client timestamp as trusted identity.
function createHandler(store,{origins=['https://birationalclass.github.io'],secret,sendMail,
  mailReady=false,teacherAccount='smeng',teacherEmail='smeng@math.ecnu.edu.cn',workspace,configureAI,now=Date.now}={}){
 const digest=value=>createHmac('sha256',secret).update(value).digest('hex');
 function identity(value){
  if(typeof value!=='string')throw fault(400,'请输入 11 位学号。');
  const studentId=value.trim();
  if(studentId===teacherAccount||studentId.toLowerCase()===teacherEmail.toLowerCase())return {studentId:teacherAccount,email:teacherEmail,role:'teacher'};
  if(!/^\d{11}$/.test(studentId))throw fault(400,'请输入 11 位学号。');
  return {studentId,email:studentId+'@stu.ecnu.edu.cn',role:'student'};
 }
 function validatePassword(value){
  if(typeof value!=='string'||value.length<10||value.length>128)throw fault(400,'密码需为 10–128 个字符。');
 }
 return async function handle(event){
  const at=now(),h=Object.fromEntries(Object.entries(event.headers||{}).map(([k,v])=>[k.toLowerCase(),v]));
  const headers={'Content-Type':'application/json; charset=utf-8','Cache-Control':'no-store','X-Content-Type-Options':'nosniff','Vary':'Origin'};
  const send=(status,data)=>({statusCode:status,headers,body:status===204?'':JSON.stringify(data),isBase64Encoded:false});
  const ip=event.trustedIp||'gateway';
  async function rate(scope,max,period){
   const slot=Math.floor(at/period),key=hash(scope+':'+slot);
   const count=await store.transaction(async tx=>{
    const old=await tx.get('limits',key),count=(old?.count||0)+1;
    await tx.put('limits',key,{count,expiresAt:(slot+2)*period});return count;
   });
   if(count>max){headers['Retry-After']=String(Math.ceil(((slot+1)*period-at)/1000));throw fault(429,'操作较频繁，请稍后再试。');}
  }
  function newSession(user,remember){
   const token=randomBytes(32).toString('hex');
   return {token,key:hash(token),value:{studentId:user.studentId,version:user.version,expiresAt:at+(remember?30:1)*86400000}};
  }
  async function account(){
   const token=(h.authorization||'').replace(/^Bearer /,'');
   if(!/^[a-f0-9]{64}$/.test(token))throw fault(401,'请先登录。');
   const key=hash(token),session=await store.get('sessions',key);
   if(!session||session.expiresAt<=at)throw fault(401,'登录已过期，请重新登录。');
   const user=await store.get('users',session.studentId);
   if(!user||user.version!==session.version)throw fault(401,'登录已失效，请重新登录。');
   return {user,key,session};
  }
  try{
   if(h.origin&&!origins.includes(h.origin))throw fault(403,'此来源不允许访问。');
   if(h.origin)headers['Access-Control-Allow-Origin']=h.origin;
   headers['Access-Control-Expose-Headers']='Retry-After';
   if(event.httpMethod==='OPTIONS'){
    headers['Access-Control-Allow-Methods']='GET,POST,OPTIONS';headers['Access-Control-Allow-Headers']='Content-Type,Authorization';return send(204);
   }
   const path=(event.path||'').replace(/^\/homework-auth(?:-test)?(?=\/|$)/,''),method=event.httpMethod;
   if(typeof secret!=='string'||secret.length<32)throw fault(503,'登录服务尚未配置完成。');
   if(path==='/api/health'&&method==='GET'){
    await store.ready();return send(200,{ready:true,registrationAvailable:Boolean(mailReady),service:'homework-auth'});
   }
   let input=method==='GET'?(event.queryStringParameters||{}):{};
   if(method==='POST'){
    if(!origins.includes(h.origin))throw fault(403,'此来源不允许访问。');
    if(!/^application\/json\b/i.test(h['content-type']||''))throw fault(415,'请使用 JSON 请求。');
    const maxBytes=/^\/api\/batches\/[a-zA-Z0-9-]+\/pages$/.test(path)?700000:/^\/api\/submissions\/[a-zA-Z0-9-]+\/edit$/.test(path)?400000:8192;
    if(typeof event.body!=='string'||event.body.length>maxBytes*1.4)throw fault(413,'请求内容过长。');
    const raw=event.isBase64Encoded?Buffer.from(event.body,'base64').toString('utf8'):event.body;
    if(Buffer.byteLength(raw)>maxBytes)throw fault(413,'请求内容过长。');
    try{input=JSON.parse(raw);}catch{throw fault(400,'请求格式不正确。');}
    if(!input||typeof input!=='object'||Array.isArray(input))throw fault(400,'请求格式不正确。');
   }
   if(path==='/api/request-code'&&method==='POST'){
    if(!mailReady)throw fault(503,'邮箱发信服务尚未开通，请稍后再试。');
    const user=identity(input.studentId),purpose=input.purpose;
    if(!['register','reset'].includes(purpose))throw fault(400,'验证码用途不正确。');
    await rate('mail-global',300,3600000);await rate('mail-ip:'+ip,50,3600000);
    await rate('mail-account:'+user.studentId,5,3600000);
    const challengeId=randomBytes(24).toString('hex'),code=String(randomInt(1000000)).padStart(6,'0');
    await store.transaction(async tx=>{
     const current=await tx.get('challenges',user.studentId);
     if(current&&at-current.sentAt<60000){headers['Retry-After']=String(Math.ceil((current.sentAt+60000-at)/1000));throw fault(429,'请等待一分钟后再获取验证码。');}
     await tx.put('challenges',user.studentId,{challengeId,purpose,codeHash:digest(challengeId+':'+code),sentAt:at,expiresAt:at+600000,attempts:0,delivered:false});
    });
    try{await sendMail({to:user.email,code,purpose});}
    catch{
     await store.transaction(async tx=>{const c=await tx.get('challenges',user.studentId);if(c?.challengeId===challengeId)await tx.remove('challenges',user.studentId);});
     throw fault(503,'验证码邮件发送失败，请稍后重试。');
    }
    await store.transaction(async tx=>{const c=await tx.get('challenges',user.studentId);if(c?.challengeId===challengeId)await tx.put('challenges',user.studentId,{...c,delivered:true});});
    return send(200,{challengeId,email:user.email,retryAfter:60,expiresIn:600});
   }
   if(['/api/register','/api/reset-password'].includes(path)&&method==='POST'){
    const identityUser=identity(input.studentId);validatePassword(input.password);
    if(!/^\d{6}$/.test(input.code||'')||!/^[a-f0-9]{48}$/.test(input.challengeId||''))throw fault(400,'请输入邮件中的 6 位验证码。');
    await rate('verify-ip:'+ip,100,600000);await rate('verify-account:'+identityUser.studentId,20,3600000);
    const purpose=path==='/api/register'?'register':'reset',salt=randomBytes(16).toString('hex');
    const password=await passwordHash(input.password,salt);
    const result=await store.transaction(async tx=>{
     const c=await tx.get('challenges',identityUser.studentId);
     if(!c||!c.delivered||c.challengeId!==input.challengeId||c.purpose!==purpose||c.expiresAt<=at||c.attempts>=5)return {error:'验证码已失效，请重新获取。'};
     if(!same(c.codeHash,digest(c.challengeId+':'+input.code))){
      await tx.put('challenges',identityUser.studentId,{...c,attempts:c.attempts+1});return {error:'验证码不正确，请核对邮件。'};
     }
     const old=await tx.get('users',identityUser.studentId);
     // The error is revealed only after proof of mailbox ownership.
     if(purpose==='register'&&old)return {error:'该账号已注册，请登录或找回密码。'};
     if(purpose==='reset'&&!old)return {error:'该账号尚未注册，请先注册。'};
     const user={...identityUser,salt,password,createdAt:old?.createdAt||at,verifiedAt:at,version:randomBytes(16).toString('hex')};
     const session=newSession(user,input.remember===true);
     await tx.put('users',user.studentId,user);await tx.remove('challenges',user.studentId);
     await tx.put('sessions',session.key,session.value);
     return {user:publicUser(user),token:session.token,expiresAt:session.value.expiresAt};
    });
    if(result.error)throw fault(400,result.error);
    return send(200,result);
   }
   if(path==='/api/login'&&method==='POST'){
    const who=identity(input.studentId);validatePassword(input.password);
    await rate('login-ip:'+ip,100,600000);await rate('login-account:'+who.studentId,12,600000);
    const user=await store.get('users',who.studentId);
    const derived=await passwordHash(input.password,user?.salt||'homework-unknown-account');
    if(!user||!same(derived,user.password))throw fault(401,'学号或密码不正确。');
    const session=newSession(user,input.remember===true);
    // A password reset racing a login must not mint a session for the old hash.
    await store.transaction(async tx=>{const current=await tx.get('users',who.studentId);if(current?.version!==user.version)throw fault(401,'密码已更新，请重新登录。');await tx.put('sessions',session.key,session.value);});
    return send(200,{user:publicUser(user),token:session.token,expiresAt:session.value.expiresAt});
   }
   if(path==='/api/session'&&method==='GET'){
    const {user,session}=await account();return send(200,{user:publicUser(user),expiresAt:session.expiresAt});
   }
   if(path==='/api/logout'&&method==='POST'){
    const token=(h.authorization||'').replace(/^Bearer /,'');
    if(/^[a-f0-9]{64}$/.test(token))await store.transaction(tx=>tx.remove('sessions',hash(token)));
    return send(200,{ok:true});
   }
   if(path==='/api/settings/ai'&&method==='POST'&&configureAI){
    const {user}=await account();if(user.role!=='teacher')throw fault(403,'仅教师可以配置 AI。');
    await rate('settings:'+user.studentId,5,600000);validatePassword(input.password);
    if(!same(await passwordHash(input.password,user.salt),user.password))throw fault(401,'个人密码不正确。');
    await configureAI(input.apiKey);return send(200,{ok:true});
   }
   if(workspace&&/^\/api\/(workspace|batches|submissions)(\/|$)/.test(path)){
    const {user}=await account();await rate('workspace:'+user.studentId,240,60000);
    return send(200,await workspace({path,method,input,user:publicUser(user)}));
   }
   throw fault(404,'接口不存在。');
  }catch(error){
   // Never log mail addresses, passwords, verification codes or bearer tokens.
   if(!error.status)console.error('[homework-auth] operation failed');
   return send(error.status||503,{error:error.status?error.message:'服务暂时不可用，请稍后重试。'});
  }
 };
}
module.exports={createHandler};
