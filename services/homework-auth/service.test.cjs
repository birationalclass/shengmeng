const {test}=require('node:test');
const assert=require('node:assert/strict');
const {createHandler}=require('./service.cjs');
const origin='https://birationalclass.github.io',studentId='10000000001',password='a-private-password-123';
function fixture(options={}){
 let at=Date.UTC(2026,8,27),tail=Promise.resolve();const rows=new Map(),mail=[];
 const adapter={get:async(k,id)=>structuredClone(rows.get(k+':'+id)),put:async(k,id,v)=>rows.set(k+':'+id,structuredClone(v)),remove:async(k,id)=>rows.delete(k+':'+id)};
 const store={...adapter,ready:async()=>{},transaction(fn){const next=tail.then(async()=>{const snapshot=new Map(rows);try{return await fn(adapter);}catch(e){rows.clear();for(const [k,v] of snapshot)rows.set(k,v);throw e;}});tail=next.catch(()=>{});return next;}};
 const configuration={secret:'s'.repeat(48),now:()=>at,mailReady:true,sendMail:async message=>mail.push(message),...options};
 const handle=createHandler(store,configuration);
 async function call(path,body,token,extra={}){const r=await handle({path:'/homework-auth/api/'+path,httpMethod:body===undefined?'GET':'POST',headers:{origin,'content-type':'application/json',...(token?{authorization:'Bearer '+token}:{})},body:body===undefined?undefined:JSON.stringify(body),trustedIp:'fixture-ip',...extra});return {...r,data:r.body?JSON.parse(r.body):null};}
 async function request(purpose='register',id=studentId){const r=await call('request-code',{studentId:id,purpose});assert.equal(r.statusCode,200,JSON.stringify(r.data));return {studentId:id,code:mail.at(-1).code,challengeId:r.data.challengeId,password};}
 async function register(id=studentId){return call('register',await request('register',id));}
 return {call,mail,rows,store,configuration,request,register,tick:ms=>{at+=ms;}};
}
test('registration verifies the derived mailbox, hashes credentials, ignores forged identity and persists sessions',async()=>{
 const f=fixture();const proof=await f.request();assert.equal(f.mail[0].to,studentId+'@stu.ecnu.edu.cn');
 const r=await f.call('register',{...proof,email:'attacker@example.com',role:'teacher',remember:true});assert.equal(r.statusCode,200);
 assert.deepEqual(r.data.user,{studentId,email:studentId+'@stu.ecnu.edu.cn',role:'student'});
 assert.equal((await f.call('session',undefined,r.data.token)).statusCode,200);
 const stored=JSON.stringify([...f.rows]);for(const secret of [password,proof.code,r.data.token])assert.ok(!stored.includes('"'+secret+'"'));
 const restarted=createHandler(f.store,f.configuration);const session=await restarted({path:'/api/session',httpMethod:'GET',headers:{origin,authorization:'Bearer '+r.data.token}});assert.equal(session.statusCode,200);
});
test('wrong password, forged bearer, and unauthenticated access are rejected',async()=>{
 const f=fixture();await f.register();assert.equal((await f.call('login',{studentId,password:'incorrect-password'})).statusCode,401);
 assert.equal((await f.call('session')).statusCode,401);assert.equal((await f.call('session',undefined,'f'.repeat(64))).statusCode,401);
 const r=await f.call('login',{studentId,password});assert.equal(r.statusCode,200);assert.equal((await f.call('logout',{},r.data.token)).statusCode,200);assert.equal((await f.call('session',undefined,r.data.token)).statusCode,401);
});
test('codes are single use, including concurrent registrations',async()=>{
 const f=fixture(),input=await f.request();const results=await Promise.all([f.call('register',input),f.call('register',input)]);
 assert.deepEqual(results.map(r=>r.statusCode).sort(),[200,400]);assert.equal((await f.call('register',input)).statusCode,400);
});
test('wrong code attempts persist; five failures invalidate even the correct code',async()=>{
 const f=fixture(),input=await f.request();const wrong=input.code==='000000'?'000001':'000000';
 for(let i=0;i<5;i++)assert.equal((await f.call('register',{...input,code:wrong})).statusCode,400);
 assert.equal(f.rows.get('challenges:'+studentId).attempts,5);assert.equal((await f.call('register',input)).statusCode,400);
});
test('expired and superseded verification codes cannot register',async()=>{
 const f=fixture(),first=await f.request();f.tick(61000);const next=await f.request();
 assert.equal((await f.call('register',first)).statusCode,400);f.tick(600001);assert.equal((await f.call('register',next)).statusCode,400);
});
test('reset needs a reset-purpose code, changes password, and revokes every older session',async()=>{
 const f=fixture(),old=await f.register();f.tick(61000);const proof=await f.request('reset');
 assert.equal((await f.call('register',proof)).statusCode,400);
 const fresh=await f.call('reset-password',{...proof,password:'my-new-password-456'});assert.equal(fresh.statusCode,200);
 assert.equal((await f.call('session',undefined,old.data.token)).statusCode,401);
 assert.equal((await f.call('login',{studentId,password})).statusCode,401);
 assert.equal((await f.call('login',{studentId,password:'my-new-password-456'})).statusCode,200);
});
test('expiry is checked even before TTL cleanup',async()=>{
 const f=fixture(),r=await f.register();f.tick(86400001);assert.equal((await f.call('session',undefined,r.data.token)).statusCode,401);
});
test('mail delivery failure leaves no usable challenge or user',async()=>{
 const f=fixture({sendMail:async()=>{throw Error('SMTP private detail');}});const r=await f.call('request-code',{studentId,purpose:'register'});
 assert.equal(r.statusCode,503);assert.ok(!r.body.includes('SMTP private'));assert.equal(f.rows.has('challenges:'+studentId),false);assert.equal(f.rows.has('users:'+studentId),false);
});
test('mail cooldown is atomic and request body cannot choose the recipient',async()=>{
 const f=fixture();const results=await Promise.all([f.call('request-code',{studentId,purpose:'register',email:'evil@example.com'}),f.call('request-code',{studentId,purpose:'register'})]);
 assert.deepEqual(results.map(r=>r.statusCode).sort(),[200,429]);assert.equal(f.mail.length,1);assert.equal(f.mail[0].to,studentId+'@stu.ecnu.edu.cn');
});
test('teacher identity can only be established through the teacher mailbox',async()=>{
 const f=fixture(),r=await f.register('smeng');assert.equal(f.mail[0].to,'smeng@math.ecnu.edu.cn');assert.equal(r.data.user.role,'teacher');
 assert.equal((await f.call('request-code',{studentId:'another-teacher',purpose:'register'})).statusCode,400);
});
test('CORS, malformed requests, body limits, and missing server setup fail closed',async()=>{
 const f=fixture();assert.equal((await f.call('request-code',{},null,{headers:{origin:'https://evil.example'}})).statusCode,403);
 assert.equal((await f.call('request-code',{},null,{headers:{'content-type':'application/json'}})).statusCode,403);
 assert.equal((await f.call('request-code',{},null,{body:'{'})).statusCode,400);
 assert.equal((await f.call('request-code',[],null)).statusCode,400);
 assert.equal((await f.call('request-code',{},null,{body:'x'.repeat(13000)})).statusCode,413);
 const preflight=await f.call('health',undefined,null,{httpMethod:'OPTIONS'});assert.equal(preflight.statusCode,204);assert.match(preflight.headers['Access-Control-Allow-Headers'],/Authorization/);
 assert.equal((await fixture({secret:''}).call('health')).statusCode,503);
 const unconfigured=fixture({mailReady:false});assert.equal((await unconfigured.call('health')).data.registrationAvailable,false);assert.equal((await unconfigured.call('request-code',{studentId,purpose:'register'})).statusCode,503);
});
test('login throttling is shared in storage across invocations',async()=>{
 const f=fixture();for(let i=0;i<12;i++)assert.equal((await f.call('login',{studentId,password})).statusCode,401);
 assert.equal((await f.call('login',{studentId,password})).statusCode,429);
});
