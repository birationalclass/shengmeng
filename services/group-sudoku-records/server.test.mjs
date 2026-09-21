import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {createRequire} from 'node:module';
import {createRecordsServer} from './server.mjs';
const model=createRequire(import.meta.url)('../../courses/abstract-algebra/2026-fall/lesson-1/associativity-sudoku.js');
const sid='20250000001',roster=[{id:sid,name:'张三',initials:'ZS'},{id:'20250000002',name:'另一测试',initials:'LYCS'}],secret='test-only-signing-secret-0123456789012345',adminPassword='demo-pass';
const boards=()=>Object.fromEntries(Array.from({length:8},(_,i)=>[i+2,model.completeForced(model.initial(i+2)).values]));
async function start(dbPath,now){const app=createRecordsServer({dbPath,roster,secret,adminPassword,origins:['http://localhost:8781'],now});await new Promise(r=>app.server.listen(0,'127.0.0.1',r));const base='http://127.0.0.1:'+app.server.address().port;
 return {...app,call:async(path,{method='GET',body,token,origin='http://localhost:8781'}={})=>{const r=await fetch(base+path,{method,headers:{Origin:origin,...(body?{'Content-Type':'application/json'}:{}),...(token?{Authorization:'Bearer '+token}:{})},...(body?{body:JSON.stringify(body)}:{})});return {status:r.status,data:r.status===204?null:await r.json()};}};}
test('server persists verified completions, idempotent retries, public masked records and teacher records across restarts',async()=>{
 const dir=mkdtempSync(join(tmpdir(),'sudoku-record-test-')),db=join(dir,'records.sqlite');let time=Date.now(),a=await start(db,()=>time);
 try{
  assert.equal((await a.call('/api/lookup',{method:'POST',body:{studentId:'123'}})).status,400);
  assert.equal((await a.call('/api/lookup',{method:'POST',body:{studentId:'99999999999'}})).status,404);
  assert.equal((await a.call('/api/lookup',{method:'POST',body:{studentId:sid},origin:'https://evil.example'})).status,403);
  const lookup=await a.call('/api/lookup',{method:'POST',body:{studentId:sid}});assert.equal(lookup.data.name,'张三');
  const input={studentId:sid,name:'张三',lookupToken:lookup.data.lookupToken,submissionId:crypto.randomUUID(),boards:boards()};
  assert.equal((await a.call('/api/completions',{method:'POST',body:{...input,boards:{9:input.boards[9]}}})).status,400);
  assert.equal((await a.call('/api/completions',{method:'POST',body:{...input,name:'wrong'}})).status,400);
  const bad=boards();bad[9][0]=bad[9][0]===1?2:1;assert.equal((await a.call('/api/completions',{method:'POST',body:{...input,boards:bad}})).status,400);
  const first=await a.call('/api/completions',{method:'POST',body:input});assert.equal(first.status,200);assert.equal(first.data.record.name,'ZS');assert.equal(first.data.record.completedLevels,8);assert.notEqual(first.data.record.studentId,sid);
  time+=60000;const retry=await a.call('/api/completions',{method:'POST',body:input});assert.equal(retry.data.record.updatedAt,first.data.record.updatedAt);
  const changed=await a.call('/api/completions',{method:'POST',body:{...input,submissionId:crypto.randomUUID()}});assert.equal(changed.data.record.firstCompletedAt,first.data.record.firstCompletedAt);assert.notEqual(changed.data.record.updatedAt,first.data.record.updatedAt);
  assert.equal((await a.call('/api/admin/records')).status,401);assert.equal((await a.call('/api/records')).data.records[0].studentId,'202****0001');
  const login=await a.call('/api/admin/session',{method:'POST',body:{password:adminPassword}});const list=await a.call('/api/admin/records',{token:login.data.token});assert.equal(list.data.records.length,1);assert.equal(list.data.records[0].studentId,sid);assert.equal(list.data.records[0].name,'张三');
  await a.close();a=await start(db,()=>time);const saved=await a.call('/api/records');assert.equal(saved.data.records.length,1);assert.equal(saved.data.records[0].name,'ZS');assert.ok(!JSON.stringify(saved.data).includes('张三'));
  time+=31*60000;assert.equal((await a.call('/api/admin/records',{token:login.data.token})).status,401);assert.equal((await a.call('/api/completions',{method:'POST',body:input})).status,401);
 }finally{await a.close();rmSync(dir,{recursive:true,force:true});}
});
test('roster lookup is rate-limited and never lists the whole roster',async()=>{const a=await start(':memory:');try{assert.equal((await a.call('/api/students')).status,404);for(let i=0;i<20;i++)assert.equal((await a.call('/api/lookup',{method:'POST',body:{studentId:sid}})).status,200);assert.equal((await a.call('/api/lookup',{method:'POST',body:{studentId:sid}})).status,429);}finally{await a.close();}});
