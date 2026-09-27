const {test}=require('node:test'),assert=require('node:assert/strict');
const {createWorkspace}=require('./workspace.cjs');
const {encrypt,decrypt}=require('./secrets.cjs');
const teacher={studentId:'smeng',role:'teacher'},student={studentId:'10000000001',role:'student'},other={studentId:'10000000002',role:'student'};
function fixture(){
 const rows=new Map();let tail=Promise.resolve();
 const access={get:async(k,id)=>structuredClone(rows.get(k+':'+id)),put:async(k,id,v)=>rows.set(k+':'+id,structuredClone(v)),remove:async(k,id)=>rows.delete(k+':'+id)};
 const store={...access,find:async(k,q,limit,offset=0)=>[...rows].filter(([key,v])=>key.startsWith(k+':')&&Object.entries(q).every(([field,value])=>v[field]===value)).map(([,v])=>structuredClone(v)).slice(offset,offset+limit),transaction(fn){const p=tail.then(async()=>{const snapshot=new Map(rows);try{return await fn(access);}catch(e){rows.clear();for(const [k,v]of snapshot)rows.set(k,v);throw e;}});tail=p.catch(()=>{});return p;}};
 let phase,subs;const ai={ready:true,model:'gpt-6-sol',effort:'medium',start:async input=>{phase=input.phase;subs=input.submissions;return {id:'resp_fixture_'+phase,cursor:0};},poll:async()=>({status:'completed',cursor:1,usage:{input_tokens:100,output_tokens:70,output_tokens_details:{reasoning_tokens:30}},text:JSON.stringify(phase==='recognize'?{submissions:[{studentId:student.studentId,name:'虚构学生',pages:[1],blocks:[{id:'p1-b1',page:1,text:'1+1=3',bbox:[.1,.2,.6,.1],uncertain:false}]}]}:{submissions:subs.map(s=>({id:s.id,summary:'注意运算。',annotations:[{blockId:'p1-b1',kind:'error',comment:'加法计算有误。',correction:'1+1=2'}]}))})})};
 const workspace=createWorkspace(store,ai);
 const call=(path,input,user=teacher)=>workspace({path:'/api/'+path,method:input===undefined?'GET':'POST',input:input||{},user});
 async function prepare(){const {batch}=await call('batches',{title:'虚构测试作业'});await call('batches/'+batch.id+'/pages',{number:1,data:Buffer.from([255,216,255,217]).toString('base64')});await call('batches/'+batch.id+'/start',{phase:'recognize'});await call('batches/'+batch.id+'/poll',{});const done=await call('batches/'+batch.id+'/poll',{});return {batch:done.batch,submission:(await call('submissions/'+done.batch.submissionIds[0])).submission};}
 return {rows,store,ai,call,prepare};
}
test('teacher upload -> OCR -> one grading -> two-view anchors -> review, usage persists',async()=>{
 const f=fixture(),r=await f.prepare();assert.equal(r.batch.status,'review');assert.equal(r.batch.usage.length,2);assert.equal(r.submission.blocks[0].text,'1+1=3');assert.equal(r.submission.annotations[0].blockId,r.submission.blocks[0].id);assert.equal(r.submission.published,false);assert.equal('score'in r.submission,false);
});
test('students cannot list batches, upload, start AI or see unpublished work',async()=>{
 const f=fixture(),r=await f.prepare();
 for(const [path,body] of [['batches',undefined],['batches',{title:'forged'}],['batches/'+r.batch.id+'/start',{phase:'grade'}],['batches/'+r.batch.id+'/pages/1',undefined]])await assert.rejects(f.call(path,body,student),e=>e.status===403);
 assert.deepEqual((await f.call('submissions',undefined,student)).submissions,[]);await assert.rejects(f.call('submissions/'+r.submission.id,undefined,student),e=>e.status===404);
});
test('publication grants only the confirmed student access, including raster pages',async()=>{
 const f=fixture(),r=await f.prepare(),id=r.submission.id;
 await f.call('submissions/'+id+'/publish',{confirmed:true,studentId:student.studentId,revision:r.submission.revision});
 assert.equal((await f.call('submissions',undefined,student)).submissions.length,1);
 assert.equal((await f.call('submissions/'+id,undefined,student)).submission.id,id);
 assert.ok((await f.call('submissions/'+id+'/pages/1',undefined,student)).page.data);
 for(const p of ['submissions/'+id,'submissions/'+id+'/pages/1'])await assert.rejects(f.call(p,undefined,other),e=>e.status===404);
 await assert.rejects(f.call('submissions/'+id+'/pages/2',undefined,student),e=>e.status===404);
 await assert.rejects(f.call('submissions/'+id+'/publish',{confirmed:true,studentId:other.studentId,revision:3},student),e=>e.status===403);
});
test('editing the transcript retracts publication and invalidates stale feedback',async()=>{
 const f=fixture(),r=await f.prepare(),id=r.submission.id;
 const published=await f.call('submissions/'+id+'/publish',{confirmed:true,studentId:student.studentId,revision:r.submission.revision});
 const edited=await f.call('submissions/'+id+'/edit',{revision:published.submission.revision,blocks:[{id:'p1-b1',text:'1+1=2',uncertain:false}]});
 assert.equal(edited.submission.published,false);assert.equal(edited.submission.annotations.length,0);
 await assert.rejects(f.call('submissions/'+id,undefined,student),e=>e.status===404);
 await assert.rejects(f.call('submissions/'+id+'/publish',{confirmed:true,studentId:student.studentId,revision:edited.submission.revision}),e=>e.status===409);
});
test('missing key fails before starting and does not simulate AI results',async()=>{
 const f=fixture();f.ai.ready=false;const {batch}=await f.call('batches',{title:'test'});
 await f.call('batches/'+batch.id+'/pages',{number:1,data:'/9j/2Q=='});
 await assert.rejects(f.call('batches/'+batch.id+'/start',{phase:'recognize'}),e=>e.status===503);
 assert.equal(f.rows.get('batches:'+batch.id).status,'uploading');assert.equal(f.rows.has('submissions:'+batch.id+'-0'),false);
});
test('malformed model geometry cannot be published and charged usage remains visible',async()=>{
 const f=fixture();f.ai.poll=async()=>({status:'completed',cursor:2,usage:{input_tokens:321,output_tokens:123},text:JSON.stringify({submissions:[{studentId:null,name:'',pages:[1],blocks:[{id:'b',page:1,text:'?',uncertain:true,bbox:[.9,.1,.8,.2]}]}]})});
 const {batch}=await f.call('batches',{title:'invalid'});await f.call('batches/'+batch.id+'/pages',{number:1,data:'/9j/2Q=='});await f.call('batches/'+batch.id+'/start',{});const result=await f.call('batches/'+batch.id+'/poll',{});
 assert.equal(result.batch.status,'failed');assert.equal(result.batch.usage[0].input_tokens,321);assert.equal(result.batch.submissionIds.length,0);
});
test('secret settings are authenticated encrypted values',()=>{const secret='s'.repeat(64),key='sk-test-fixture-key';const encoded=encrypt(key,secret);assert.ok(!JSON.stringify(encoded).includes(key));assert.equal(decrypt(encoded,secret),key);assert.throws(()=>decrypt(encoded,'different-secret'));});
