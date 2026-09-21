import test from 'node:test';
import assert from 'node:assert/strict';
import {DatabaseSync} from 'node:sqlite';
import {readFileSync,mkdtempSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {createRequire} from 'node:module';
import worker,{handle,verifiedBoards} from './worker.mjs';
import clues from './clues.mjs';
const model=createRequire(import.meta.url)('../../../courses/abstract-algebra/2026-fall/lesson-1/associativity-sudoku.js');
const boards=()=>Object.fromEntries(Array.from({length:8},(_,i)=>[i+2,model.completeForced(model.initial(i+2)).values]));
const roster=[['20250000001','张三','ZS'],['20250000002','李四','LS']];
function setup(path=':memory:'){
 const db=new DatabaseSync(path);db.exec('PRAGMA foreign_keys=ON;'+readFileSync(new URL('./schema.sql',import.meta.url),'utf8'));
 for(const row of roster)db.prepare('INSERT OR IGNORE INTO students VALUES(?,?,?)').run(...row);
 const prepare=(sql,args=[])=>({bind:(...values)=>prepare(sql,values),first:async()=>db.prepare(sql).get(...args)||null,all:async()=>({results:db.prepare(sql).all(...args)}),run:async()=>({success:true,meta:db.prepare(sql).run(...args)})});
 const env={DB:{prepare},RECORDS_SECRET:'test-only-secret-0123456789-abcdefghijklmnopqrstuvwxyz',RECORDS_ADMIN_PASSWORD:'test-only-password-012345',RECORDS_ORIGINS:'https://birationalclass.github.io'};
 let now=Date.now();
 const call=async(path,{method='GET',body,token,origin='https://birationalclass.github.io',ip='192.0.2.1'}={})=>{
  const res=await handle(new Request('https://records.test'+path,{method,headers:{Origin:origin,'CF-Connecting-IP':ip,...(body?{'Content-Type':'application/json'}:{}),...(token?{Authorization:'Bearer '+token}:{})},...(body?{body:JSON.stringify(body)}:{})}),env,now);
  return {status:res.status,headers:res.headers,data:res.status===204?null:await res.json()};
 };
 return {db,env,call,advance:delta=>{now+=delta;},close:()=>db.close()};
}
test('precomputed clues match the live game and all eight valid tables pass',()=>{
 for(let n=2;n<=9;n++)assert.deepEqual(clues[n],model.initial(n));assert.equal(verifiedBoards(boards()),true);
 assert.equal(verifiedBoards({}),false);const bad=boards();bad[9][0]=100;assert.equal(verifiedBoards(bad),false);
});
test('Worker entry, CORS, registration, initials, teacher auth and persistence',async()=>{
 const dir=mkdtempSync(join(tmpdir(),'sudoku-worker-')),file=join(dir,'records.sqlite');let a=setup(file);
 try{
  const health=await worker.fetch(new Request('https://records.test/api/health'),a.env,{});assert.equal(health.status,200);
  assert.equal((await a.call('/api/health',{origin:'https://evil.test'})).status,403);
  assert.equal((await a.call('/api/health',{method:'OPTIONS'})).status,204);
  assert.equal((await a.call('/api/lookup',{method:'POST',body:{studentId:'123'}})).status,400);
  const lookup=await a.call('/api/lookup',{method:'POST',body:{studentId:roster[0][0]}});assert.equal(lookup.data.name,'张三');
  const input={studentId:roster[0][0],name:'张三',lookupToken:lookup.data.lookupToken,submissionId:crypto.randomUUID(),boards:boards()};
  assert.equal((await a.call('/api/completions',{method:'POST',body:{...input,name:'李四'}})).status,400);
  assert.equal((await a.call('/api/completions',{method:'POST',body:{...input,boards:{}}})).status,400);
  const save=await a.call('/api/completions',{method:'POST',body:input});assert.equal(save.status,200);assert.equal(save.data.record.name,'ZS');
  a.advance(1000);const retry=await a.call('/api/completions',{method:'POST',body:input});assert.equal(retry.data.record.updatedAt,save.data.record.updatedAt);
  const update=await a.call('/api/completions',{method:'POST',body:{...input,submissionId:crypto.randomUUID()}});assert.equal(update.data.record.firstCompletedAt,save.data.record.firstCompletedAt);assert.notEqual(update.data.record.updatedAt,save.data.record.updatedAt);
  const publicList=await a.call('/api/records');assert.equal(publicList.data.records[0].studentId,'202****0001');assert.ok(!JSON.stringify(publicList.data).includes('张三'));assert.ok(!JSON.stringify(publicList.data).includes(roster[0][0]));
  assert.equal((await a.call('/api/admin/records')).status,401);
  assert.equal((await a.call('/api/admin/session',{method:'POST',body:{password:'wrong'}})).status,401);
  const login=await a.call('/api/admin/session',{method:'POST',body:{password:a.env.RECORDS_ADMIN_PASSWORD}});
  assert.equal((await a.call('/api/admin/records',{token:login.data.token})).data.records[0].name,'张三');
  const lookup2=await a.call('/api/lookup',{method:'POST',body:{studentId:roster[1][0]}});
  assert.equal((await a.call('/api/completions',{method:'POST',body:{...input,studentId:roster[1][0],name:'李四',lookupToken:lookup2.data.lookupToken}})).status,409);
  a.advance(31*60000);assert.equal((await a.call('/api/admin/records',{token:login.data.token})).status,401);
  assert.equal((await a.call('/api/completions',{method:'POST',body:input})).status,401);
  a.close();a=setup(file);assert.equal((await a.call('/api/records')).data.records[0].name,'ZS');
 }finally{a.close();rmSync(dir,{recursive:true,force:true});}
});
test('sensitive endpoint throttles persist across isolates, malformed bodies fail, and cron cleans stale limits',async()=>{
 const a=setup();try{
  for(let i=0;i<20;i++)assert.equal((await a.call('/api/lookup',{method:'POST',body:{studentId:roster[0][0]}})).status,200);
  assert.equal((await a.call('/api/lookup',{method:'POST',body:{studentId:roster[0][0]}})).status,429);
  assert.equal((await a.call('/api/students')).status,404);
  const huge=await handle(new Request('https://records.test/api/lookup',{method:'POST',headers:{'Content-Type':'application/json','CF-Connecting-IP':'192.0.2.2'},body:JSON.stringify({studentId:'x'.repeat(17000)})}),a.env);assert.equal(huge.status,413);
  a.db.prepare('INSERT INTO rate_limits VALUES(?,?,?)').run('old',1,1);await worker.scheduled({},a.env);assert.equal(a.db.prepare('SELECT * FROM rate_limits WHERE key=?').get('old'),undefined);
 }finally{a.close();}
});
