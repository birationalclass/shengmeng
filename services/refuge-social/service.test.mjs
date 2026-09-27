import {test} from 'node:test';
import assert from 'node:assert/strict';
import {createRequire} from 'node:module';
const {createHandler}=createRequire(import.meta.url)('./service.cjs');
function setup(ai=null){const map=new Map();let time=Date.now();const store={async aiHistory(userId){return [...map.entries()].filter(([k,v])=>k.startsWith("ai_jobs")&&v.userId===userId).map(([,v])=>v);},async update(k,id,v){map.set(k+id,{...map.get(k+id),...v});},async users(after){return [...map.entries()].filter(([k,v])=>k.startsWith("users")&&v.id>after).map(([,v])=>v).sort((a,b)=>a.id.localeCompare(b.id)).slice(0,51);},async get(k,id){return map.get(k+id);},async put(k,id,v){map.set(k+id,v);},async remove(k,id){map.delete(k+id);},async create(k,id,v){if(map.has(k+id))return false;map.set(k+id,v);return true;},async rate(id){const n=(map.get(id)||0)+1;map.set(id,n);return n;},async messages(){return [...map.entries()].filter(([k])=>k.startsWith('messages')).map(([,v])=>v).sort((a,b)=>b.createdAt-a.createdAt).slice(0,50);}};const handle=createHandler(store,{now:()=>time,ai});return {map,advance:ms=>time+=ms,async call(path,data,cookie='',origin='https://birationalclass.github.io'){const r=await handle({path:'/refuge/api/'+path,httpMethod:data?'POST':'GET',headers:{origin,cookie,'content-type':'application/json'},body:JSON.stringify(data),trustedIp:'test'});return {...r,data:JSON.parse(r.body),cookie:r.headers['Set-Cookie']?.split(';')[0]};}};}
test('registration logs in with HttpOnly cookie; password hashes stay private, logout revokes',async()=>{const b=setup(),r=await b.call('register',{name:'Test_账号',password:'a-strong-test-password'});assert.equal(r.statusCode,200);assert.match(r.headers['Set-Cookie'],/HttpOnly/);assert.match(r.headers['Set-Cookie'],/Secure; SameSite=None; Partitioned/);assert.ok(!r.body.includes('password'));assert.equal((await b.call('session',null,r.cookie)).data.user.name,'Test_账号');const stored=[...b.map.entries()].find(([k])=>k.startsWith('users'))[1];assert.notEqual(stored.password,'a-strong-test-password');assert.equal((await b.call('logout',{},r.cookie)).statusCode,200);assert.equal((await b.call('session',null,r.cookie)).statusCode,401);});
test('wrong password, duplicate account, disallowed origin, session expiry',async()=>{const b=setup(),credentials={name:'alice',password:'correct-test-password'};const first=await b.call('register',credentials);assert.equal((await b.call('register',{...credentials,name:'ALICE'})).statusCode,409);assert.equal((await b.call('login',{...credentials,password:'incorrect-password'})).statusCode,401);assert.equal((await b.call('login',credentials,'','https://evil.test')).statusCode,403);const login=await b.call('login',{...credentials,remember:false});assert.equal(login.statusCode,200);assert.ok(!login.headers['Set-Cookie'].includes('Max-Age'));b.advance(31*86400000);assert.equal((await b.call('session',null,first.cookie)).statusCode,401);});
test('two accounts exchange server messages, retry is idempotent, sender cannot be forged',async()=>{const b=setup(),a=await b.call('register',{name:'alice',password:'correct-test-password'}),c=await b.call('register',{name:'bob',password:'correct-test-password'});const input={id:'aaaaaaaa-aaaa-aaaa-aaaa-aaaaaaaaaaaa',text:'<img src=x onerror=alert(1)>',name:'forged'};assert.equal((await b.call('messages',input)).statusCode,401);assert.equal((await b.call('messages',input,a.cookie)).statusCode,200);await b.call('messages',input,a.cookie);const list=await b.call('messages',null,c.cookie);assert.equal(list.data.messages.length,1);assert.equal(list.data.messages[0].name,'alice');assert.equal(list.data.messages[0].mine,false);assert.equal((await b.call('messages',{...input,text:'x'.repeat(301)},a.cookie)).statusCode,400);b.advance(8*86400000);assert.equal((await b.call('messages',null,c.cookie)).data.messages.length,1);});
test('login and message limits apply server-side',async()=>{const b=setup(),r=await b.call('register',{name:'alice',password:'correct-test-password'});let last;for(let i=0;i<13;i++)last=await b.call('messages',{id:'aaaaaaaa-aaaa-aaaa-aaaa-aaaaaaaaaaaa',text:'hello'},r.cookie);assert.equal(last.statusCode,429);});

test('admin listing and mute permissions, expiry and unmute',async()=>{
 const b=setup(),a=await b.call('register',{name:'manager',password:'test-password',role:'admin'}),m=await b.call('register',{name:'member',password:'test-password'});
 assert.equal(a.data.user.role,'member');assert.equal((await b.call('admin/users',{},m.cookie)).statusCode,403);
 const key='users'+a.data.user.id;b.map.set(key,{...b.map.get(key),role:'admin'});
 const list=await b.call('admin/users',{},a.cookie);assert.equal(list.statusCode,200);assert.equal(list.data.users.length,2);assert.ok(!list.body.includes('password'));assert.ok(list.data.users.every(u=>u.lastLoginAt));
 const input={userId:m.data.user.id,seconds:3600};assert.equal((await b.call('admin/mute',input,m.cookie)).statusCode,403);
 assert.equal((await b.call('admin/mute',input,a.cookie)).statusCode,200);
 const msg={id:'aaaaaaaa-aaaa-aaaa-aaaa-aaaaaaaaaaaa',text:'hello'};assert.equal((await b.call('messages',msg,m.cookie)).statusCode,403);assert.equal((await b.call('messages',null,m.cookie)).statusCode,200);
 b.advance(3600001);assert.equal((await b.call('messages',msg,m.cookie)).statusCode,200);
 await b.call('admin/mute',input,a.cookie);await b.call('admin/mute',{...input,seconds:0},a.cookie);assert.equal((await b.call('messages',msg,m.cookie)).statusCode,200);
 assert.equal((await b.call('admin/mute',{userId:a.data.user.id,seconds:3600},a.cookie)).statusCode,400);
});

test('AI jobs are private, idempotent, exclude screenshots and require admin configuration',async()=>{
 let starts=0;const ai={list:async()=>[],save:async()=>{},start:async()=>{starts++;return {status:'completed',text:'Answer'};}};
 const b=setup(ai),a=await b.call('register',{name:'alice',password:'test-password'}),c=await b.call('register',{name:'bobby',password:'test-password'});
 const input={id:'aaaaaaaa-aaaa-aaaa-aaaa-aaaaaaaaaaaa',provider:'openai',image:'data:image/jpeg;base64,'+Buffer.concat([Buffer.from([255,216,255]),Buffer.alloc(300000)]).toString('base64'),question:'Explain'};
 assert.equal((await b.call('ai/start',input)).statusCode,401);
 assert.equal((await b.call('admin/ai',{},a.cookie)).statusCode,403);
 assert.equal((await b.call('ai/start',{...input,image:'invalid'},a.cookie)).statusCode,400);
 const r=await b.call('ai/start',input,a.cookie);assert.equal(r.statusCode,200);assert.equal(r.data.job.text,'Answer');
 await b.call('ai/start',input,a.cookie);assert.equal(starts,1);
 assert.equal((await b.call('ai/poll',{id:r.data.job.id},c.cookie)).statusCode,404);
 assert.equal((await b.call('ai/history',null,c.cookie)).data.jobs.length,0);
 assert.equal((await b.call('ai/history',null,a.cookie)).data.jobs.length,1);
 assert.equal((await b.call('messages',null,c.cookie)).data.messages.length,0);
 assert.ok(!JSON.stringify([...b.map.values()]).includes('data:image'));
});

test('unified identification routes existing and new names without creating an account',async()=>{
 const b=setup();assert.equal((await b.call('identify',{name:'freshname'})).data.next,'register');
 assert.equal([...b.map.keys()].filter(k=>k.startsWith('users')).length,0);
 await b.call('register',{name:'Alice',password:'test-password'});
 assert.deepEqual((await b.call('identify',{name:' ALICE '})).data,{next:'login'});
 assert.equal((await b.call('identify',{name:'<invalid>'})).statusCode,400);
 assert.equal((await b.call('identify',{name:'Alice'},'','https://evil.test')).statusCode,403);
 for(let i=0;i<12;i++)await b.call('identify',{name:'randomname'});
 assert.equal((await b.call('identify',{name:'Alice'})).statusCode,429);
});
