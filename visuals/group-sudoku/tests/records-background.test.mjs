import test from 'node:test';import assert from 'node:assert/strict';
// Load configuration with no browser window, so the warmup makes no real request.
globalThis.location={hostname:'localhost'};
const {createCompletionRecords}=await import('../records.mjs');delete globalThis.location;
class Element extends EventTarget{
 constructor(){super();this.value='';this.textContent='';this.dataset={};this.hidden=false;this.open=false;this.style={setProperty(){}};}
 showModal(){this.open=true;}close(){this.open=false;}focus(){}
}
test('local entry resolves before login; recovery migrates and retries the same pending submission',async()=>{
 const saved=Object.fromEntries(['document','window','innerHeight'].map(k=>[k,globalThis[k]])),els=new Map(),el=id=>{if(!els.has(id))els.set(id,new Element());return els.get(id);};
 const doc=new EventTarget();doc.getElementById=el;doc.documentElement=new Element();const win=new EventTarget();
 Object.assign(globalThis,{document:doc,window:win,innerHeight:844});
 try{
  const values=new Map(),storage={getItem:k=>values.get(k),setItem:(k,v)=>values.set(k,v)},campaign={completed:[],finished:{}},logins=[],calls=[];let hooks,failSave=true;
  const records=createCompletionRecords({storage,t:zh=>zh,getCampaign:()=>campaign,onLogin:data=>logins.push(data),connectionFactory:value=>{hooks=value;return {wake(){},pause(){}};},api:async(path,options)=>{
   calls.push({path,options});if(path==='/api/health')return {ready:true};
   if(path==='/api/login')return {account:{id:'guest_test',kind:'guest',name:'QA'},sessionToken:'test-session',boards:{}};
   if(path==='/api/progress'){if(failSave)throw Object.assign(Error('disconnected'),{status:503});return {saved:true,record:{completedLevels:1}};}
  }});
  const entered=records.start();await el('guestLogin').onclick();await entered;
  assert.equal(el('playerDialog').open,false);assert.equal(calls.length,0);assert.equal(logins[0].local,true);assert(logins[0].account.id.startsWith('local-guest-'));
  campaign.completed=[2];campaign.finished={2:[2,1,1,2]};records.completed();
  const original=JSON.parse(values.get('group-sudoku-pending:'+logins[0].account.id));
  await assert.rejects(()=>hooks.run({signal:new AbortController().signal}),/disconnected/);
  const migrated=JSON.parse(values.get('group-sudoku-pending:guest_test'));assert.equal(migrated.submissionId,original.submissionId);assert.equal(logins[1].local,false);
  failSave=false;await hooks.run({signal:new AbortController().signal});
  const saves=calls.filter(c=>c.path==='/api/progress');assert.equal(saves.length,2);assert.equal(saves[0].options.body.submissionId,saves[1].options.body.submissionId);assert.equal(values.get('group-sudoku-pending:guest_test'),'null');assert.equal(calls.filter(c=>c.path==='/api/login').length,1);
 }finally{for(const[k,v]of Object.entries(saved)){if(v===undefined)delete globalThis[k];else globalThis[k]=v;}}
});
