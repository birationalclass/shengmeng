import test from 'node:test';
import assert from 'node:assert/strict';
import {createRequire} from 'node:module';
import {handle} from './service.mjs';
import {createStore} from './store.mjs';
const model=createRequire(import.meta.url)('../../../courses/abstract-algebra/2026-fall/lesson-1/associativity-sudoku.js');
const boards=()=>Object.fromEntries(Array.from({length:8},(_,i)=>[i+2,model.completeForced(model.initial(i+2)).values]));
// SDK-shaped transactional fake: cloud deployment smoke tests exercise the real database.
function database(){
 const tables=new Map();let queue=Promise.resolve();
 const collection=(name,inTx=false)=>{
  if(!tables.has(name))tables.set(name,new Map());const table=tables.get(name);let offset=0,limit=100;
  const query={doc:id=>({get:async()=>({data:inTx?(table.get(id)||null):(table.has(id)?[table.get(id)]:[])}),set:async value=>{table.set(id,structuredClone(value));}}),
   orderBy:()=>query,skip:n=>{offset=n;return query;},limit:n=>{limit=n;return query;},get:async()=>({data:[...table.values()].slice(offset,offset+limit)})};return query;
 };
 return {collection,runTransaction:fn=>{const next=queue.then(()=>fn({collection:name=>collection(name,true)}));queue=next.catch(()=>{});return next;}};
}
test('CloudBase preserves first completion, atomic retries, privacy and teacher access',async()=>{
 const db=database();for(const [id,name,initials] of [['20250000001','张三','ZS'],['20250000002','李四','LS']])await db.collection('test_students').doc(id).set({id,name,initials});
 const env={store:createStore(db,'test_'),secret:'test-only-abcdefghijklmnopqrstuvwxyz-0123456789',password:'demo-pass',identity:'test-user'};
 let now=Date.now();const call=(path,body,token)=>handle({path,method:body?'POST':'GET',body,token},env,now);
 assert.equal((await handle({path:'/api/health'},{...env,identity:''})).status,401);
 assert.equal((await call('/api/health')).data.ready,true);
 const lookup=await call('/api/lookup',{studentId:'20250000001'});
 const input={studentId:'20250000001',name:'张三',lookupToken:lookup.data.lookupToken,submissionId:crypto.randomUUID(),boards:boards()};
 assert.equal((await call('/api/completions',{...input,boards:{}})).status,400);
 assert.equal((await call('/api/completions',{...input,name:'李四'})).status,400);
 const results=await Promise.all([call('/api/completions',input),call('/api/completions',input)]);
 assert.equal(results[0].status,200);assert.deepEqual(results[0].data,results[1].data);
 now+=1000;assert.equal((await call('/api/completions',input)).data.record.updatedAt,results[0].data.record.updatedAt);
 const update=await call('/api/completions',{...input,submissionId:crypto.randomUUID()});assert.equal(update.data.record.firstCompletedAt,results[0].data.record.firstCompletedAt);assert.notEqual(update.data.record.updatedAt,results[0].data.record.updatedAt);
 const rows=(await call('/api/records')).data;assert.equal(rows.total,1);assert.equal(rows.records[0].name,'ZS');assert.equal(rows.records[0].studentId,'202****0001');assert.ok(!JSON.stringify(rows).includes('张三'));
 const second=await call('/api/lookup',{studentId:'20250000002'});assert.equal((await call('/api/completions',{...input,studentId:'20250000002',name:'李四',lookupToken:second.data.lookupToken})).status,409);
 assert.equal((await call('/api/admin/records')).status,401);assert.equal((await call('/api/admin/session',{password:'bad'})).status,401);
 const login=await call('/api/admin/session',{password:env.password});assert.equal((await call('/api/admin/records',undefined,login.data.token)).data.records[0].name,'张三');
 now+=31*60000;assert.equal((await call('/api/admin/records',undefined,login.data.token)).status,401);assert.equal((await call('/api/completions',input)).status,401);
});
test('CloudBase throttles sensitive endpoints and paginates past 100 records',async()=>{
 const db=database(),store=createStore(db,'test_');await db.collection('test_students').doc('20250000001').set({id:'20250000001',name:'张三',initials:'ZS'});
 const env={store,secret:'test-only-abcdefghijklmnopqrstuvwxyz-0123456789',password:'demo-pass',identity:'test-user'};
 const now=Date.now(),event={path:'/api/lookup',method:'POST',body:{studentId:'20250000001'}};
 for(let i=0;i<20;i++)assert.equal((await handle(event,env,now)).status,200);
 assert.equal((await handle(event,env,now)).status,429);assert.equal((await handle(event,env,now+60000)).status,200);
 assert.equal((await handle({...event,body:{studentId:'x'.repeat(17000)}},env,now)).status,413);
 for(let i=0;i<129;i++)await db.collection('test_completions').doc(String(i)).set({id:String(i)});
 assert.equal((await store.records()).length,129);
});

test('HTTP gateway rejects foreign origins, malformed bodies and supports browser preflight',async()=>{
 const {handleHttp}=await import('./http.mjs');
 const env={origins:'https://birationalclass.github.io',store:{ready:async()=>true},identity:'gateway-test',secret:'abcdefghijklmnopqrstuvwxyz-0123456789',password:'demo-pass'};
 const event={path:'/records/api/health',httpMethod:'GET',headers:{origin:'https://birationalclass.github.io'}};
 const health=await handleHttp(event,env);assert.equal(health.statusCode,200);assert.equal(health.headers['Access-Control-Allow-Origin'],event.headers.origin);
 assert.equal((await handleHttp({...event,headers:{origin:'https://evil.example'}},env)).statusCode,403);
 assert.equal((await handleHttp({...event,httpMethod:'OPTIONS'},env)).statusCode,204);
 assert.equal((await handleHttp({...event,httpMethod:'POST',headers:{'content-type':'text/plain'},body:'{}'},env)).statusCode,415);
 assert.equal((await handleHttp({...event,httpMethod:'POST',headers:{'content-type':'application/json'},body:'{'},env)).statusCode,400);
});
