const {randomUUID}=require('node:crypto');
const fault=(status,message)=>Object.assign(Error(message),{status});
const requireTeacher=user=>{if(user.role!=='teacher')throw fault(403,'仅教师可以执行此操作。');};
const listItem=({id,title,createdAt,studentId,name,published,status,pages})=>({id,title,createdAt,studentId:studentId||'',name:name||'',published:Boolean(published),status,pages:pages?.length||0});
const bboxValid=v=>Array.isArray(v)&&v.length===4&&v.every(n=>typeof n==='number'&&Number.isFinite(n)&&n>=0&&n<=1)&&v[2]>0&&v[3]>0&&v[0]+v[2]<=1.001&&v[1]+v[3]<=1.001;
function transcript(value,pageCount){
 if(!Array.isArray(value?.submissions)||!value.submissions.length||value.submissions.length>pageCount)throw fault(422,'AI 转录结构不完整，请重新识别或人工核对。');
 const pageSet=new Set(),blockSet=new Set();let count=0;
 for(const s of value.submissions){
  if(s.studentId!==null&&!/^\d{11}$/.test(s.studentId||''))throw fault(422,'识别出的学号无效。');
  if(typeof s.name!=='string'||s.name.length>80||!Array.isArray(s.pages)||!s.pages.length||!Array.isArray(s.blocks)||!s.blocks.length)throw fault(422,'AI 转录结构不完整。');
  for(const p of s.pages){if(!Number.isInteger(p)||p<1||p>pageCount||pageSet.has(p))throw fault(422,'扫描页归属不唯一，需要教师核对。');pageSet.add(p);}
  for(const b of s.blocks){if(!/^[a-zA-Z0-9_-]{1,64}$/.test(b.id||'')||blockSet.has(b.id)||!s.pages.includes(b.page)||typeof b.text!=='string'||b.text.length>8000||typeof b.uncertain!=='boolean'||!bboxValid(b.bbox))throw fault(422,'原稿定位或文字转录无效。');blockSet.add(b.id);count++;}
 }
 if(pageSet.size!==pageCount||count>400)throw fault(422,'AI 未完整覆盖全部扫描页，或内容过长。');
 return value.submissions;
}
function grades(value,submissions){
 if(!Array.isArray(value?.submissions)||value.submissions.length!==submissions.length)throw fault(422,'批改结果未覆盖全部作业。');
 const seen=new Set();
 for(const grade of value.submissions){const s=submissions.find(s=>s.id===grade.id);if(!s||seen.has(grade.id)||typeof grade.summary!=='string'||grade.summary.length>8000||!Array.isArray(grade.annotations)||grade.annotations.length>400)throw fault(422,'AI 批改结构无效。');seen.add(grade.id);
  for(const a of grade.annotations)if(!s.blocks.some(b=>b.id===a.blockId)||!['correct','error','suggestion','uncertain'].includes(a.kind)||typeof a.comment!=='string'||a.comment.length>4000||typeof a.correction!=='string'||a.correction.length>4000)throw fault(422,'批注未正确对应原稿。');
 }
 return value.submissions;
}
function createWorkspace(store,ai,{now=Date.now}={}){
 async function batch(id){const b=await store.get('batches',id);if(!b)throw fault(404,'未找到这批作业。');return b;}
 async function submission(id,user){const s=await store.get('submissions',id);if(!s||(user.role!=='teacher'&&(!s.published||s.studentId!==user.studentId)))throw fault(404,'未找到这份作业。');return s;}
 async function mutate(kind,id,fn){return store.transaction(async tx=>{const row=await tx.get(kind,id);if(!row)throw fault(404,'作业不存在。');const next=await fn(row,tx);await tx.put(kind,id,next);return next;});}
 function event(b,message){return [...(b.events||[]),{at:now(),message}].slice(-60);}
 function cleanBatch(b){const {lease,request,...safe}=b;return {...safe,ai:request?{phase:request.phase,status:request.status,liveText:request.liveText||''}:null};}
 async function start(b,phase){
  if(!ai.ready)throw fault(503,'AI 尚未启用，请先配置 OpenAI API key。');
  const requestId=randomUUID();
  b=await mutate('batches',b.id,async(current,tx)=>{
   if(['recognizing','grading','starting'].includes(current.status))throw fault(409,'这批作业已经在处理中。');
   if(current.pages.length!==current.expectedPages)throw fault(409,'扫描页尚未全部上传。');
   if(phase==='grade')for(const id of current.submissionIds){const s=await tx.get('submissions',id);await tx.put('submissions',id,{...s,published:false,revision:s.revision+1});}
   return {...current,error:'',status:'starting',request:{phase,status:'starting',requestId,startedAt:now()},events:event(current,phase==='recognize'?'准备识别学生、页码与原文':'准备统一批改两种视图的内容')};
  });
  try{
   const pages=phase==='recognize'?await Promise.all(b.pages.map(id=>store.get('pages',id))):null;
   const submissions=phase==='grade'?await Promise.all(b.submissionIds.map(id=>store.get('submissions',id))):null;
   const remote=await ai.start({phase,pages,submissions,requestId});
   return await mutate('batches',b.id,current=>({...current,status:phase==='recognize'?'recognizing':'grading',request:{phase,status:'in_progress',requestId,responseId:remote.id,cursor:remote.cursor,liveText:''},events:event(current,phase==='recognize'?'AI 正在逐页识别和忠实转录':'AI 正在核查数学内容并生成批注')}));
  }catch(error){await mutate('batches',b.id,current=>({...current,status:'failed',error:error.status?error.message:'AI 请求未能确认，请检查服务后重试；上游可能已产生用量。',events:event(current,'AI 启动失败')}));throw error;}
 }
 async function poll(b){
  if(b.status==='starting'&&now()-(b.request.startedAt||0)>60000)return mutate('batches',b.id,current=>({...current,status:'failed',error:'未能确认 AI 任务是否启动，请检查用量后手动重试。'}));
  if(!['recognizing','grading'].includes(b.status)||!b.request?.responseId)return b;
  const lease=randomUUID(),at=now();
  const locked=await store.transaction(async tx=>{const current=await tx.get('batches',b.id);if(current.lease?.until>at||!['recognizing','grading'].includes(current.status))return null;const next={...current,lease:{id:lease,until:at+25000}};await tx.put('batches',b.id,next);return next;});
  if(!locked)return batch(b.id);
  let polled;
  try{
   const result=polled=await ai.poll(locked.request.responseId,locked.request.cursor);
   return await store.transaction(async tx=>{
    const current=await tx.get('batches',b.id);if(current.lease?.id!==lease)return current;
    const request={...current.request,status:result.status,cursor:result.cursor,liveText:(result.text??((current.request.liveText||'')+(result.delta||''))).slice(0,180000)};
    let next={...current,request,lease:null};
    if(['failed','cancelled','incomplete'].includes(result.status)){next.status='failed';next.error='AI 任务未完整完成（'+(result.error||result.status)+'），请复核后重试。';next.events=event(next,next.error);}
    if(result.usage)next.usage=[...(next.usage||[]),{responseId:request.responseId,phase:request.phase,...result.usage}];
    if(result.status==='completed'){
     let parsed;try{parsed=JSON.parse(result.text);}catch{throw fault(422,'AI 未返回完整的结构化结果，请重试。');}
     if(request.phase==='recognize'){
      const parts=transcript(parsed,current.pages.length);next.submissionIds=[];
      for(let i=0;i<parts.length;i++){
       const part=parts[i],id=current.id+'-'+i;next.submissionIds.push(id);
       await tx.put('submissions',id,{...part,id,batchId:current.id,title:current.title,createdAt:current.createdAt,published:false,status:'transcribed',revision:1,annotations:[],summary:''});
      }
      next.status='transcribed';next.events=event(next,'转录完成，已建立扫描版和电脑字体版对应关系');
     }else{
      const subs=[];for(const id of current.submissionIds)subs.push(await tx.get('submissions',id));
      for(const grade of grades(parsed,subs)){const s=subs.find(s=>s.id===grade.id);await tx.put('submissions',s.id,{...s,...grade,status:'review',published:false,revision:s.revision+1});}
      next.status='review';next.events=event(next,'批改完成，等待教师核对学号、转录与批注后发布');
     }
     next.request={...request,liveText:''};
    }
    await tx.put('batches',b.id,next);return next;
   });
  }catch(error){
   return mutate('batches',b.id,current=>current.lease?.id===lease?{...current,lease:null,...(error.status===422?{status:'failed'}:{}),...(polled?.usage?{usage:[...(current.usage||[]).filter(u=>u.responseId!==locked.request.responseId),{responseId:locked.request.responseId,phase:locked.request.phase,...polled.usage}]}:{}),error:error.status?error.message:'连接中断，稍后继续获取进度。'}:current);
  }
 }
 return async function workspace({path,method,input,user}){
  if(path==='/api/workspace'&&method==='GET')return {user,model:ai.model,effort:ai.effort,aiReady:ai.ready,maxPages:20,maxPageBytes:480000};
  const offset=Math.max(0,Math.min(100000,Number.parseInt(input.offset,10)||0));
  if(path==='/api/batches'&&method==='GET'){requireTeacher(user);const rows=await store.find('batches',{},50,offset);return {batches:rows.map(b=>({...listItem(b),error:b.error||''})),nextOffset:rows.length===50?offset+50:null};}
  if(path==='/api/submissions'&&method==='GET'){const where=user.role==='teacher'?{}:{studentId:user.studentId,published:true};const rows=await store.find('submissions',where,50,offset);return {submissions:rows.map(listItem),nextOffset:rows.length===50?offset+50:null};}
  if(path==='/api/batches'&&method==='POST'){
   requireTeacher(user);if(typeof input.title!=='string'||!input.title.trim()||input.title.length>100)throw fault(400,'请输入 1–100 字的作业名称。');
   const expectedPages=input.expectedPages??1;if(!Number.isInteger(expectedPages)||expectedPages<1||expectedPages>20)throw fault(400,'每批需为 1–20 页。');
   const id=randomUUID(),b={id,title:input.title.trim(),createdAt:now(),createdBy:user.studentId,expectedPages,pages:[],submissionIds:[],status:'uploading',events:[],usage:[]};await store.put('batches',id,b);return {batch:cleanBatch(b)};
  }
  const match=path.match(/^\/api\/(batches|submissions)\/([a-zA-Z0-9-]{1,80})(?:\/(pages|start|poll|publish|edit)(?:\/(\d+))?)?$/);
  if(!match)throw fault(404,'接口不存在。');
  const [,kind,id,action,pageNumber]=match;
  if(kind==='batches'){
   requireTeacher(user);let b=await batch(id);
   if(!action&&method==='GET')return {batch:cleanBatch(b)};
   if(action==='pages'&&method==='POST'){
    if(typeof input.data!=='string'||input.data.length>640000||!/^[A-Za-z0-9+/]+={0,2}$/.test(input.data))throw fault(400,'扫描页图像过大或无效。');
    const bytes=Buffer.from(input.data,'base64');if(bytes.length>480000||bytes[0]!==255||bytes[1]!==216||bytes[2]!==255)throw fault(400,'请上传有效的 JPEG 扫描页。');
    if(!Number.isInteger(input.number)||input.number<1||input.number>20)throw fault(400,'每批最多 20 页。');
    const pageId=id+'-p'+input.number;
    b=await mutate('batches',id,async(current,tx)=>{if(current.status!=='uploading')throw fault(409,'识别开始后不能替换扫描页。');if(input.number>current.pages.length+1)throw fault(400,'请按顺序上传扫描页。');await tx.put('pages',pageId,{batchId:id,number:input.number,data:input.data,width:input.width||0,height:input.height||0});const pages=[...current.pages];pages[input.number-1]=pageId;return {...current,pages};});
    return {batch:cleanBatch(b)};
   }
   if(action==='pages'&&method==='GET'&&pageNumber){const page=await store.get('pages',b.pages[Number(pageNumber)-1]||'missing');if(!page)throw fault(404,'扫描页不存在。');return {page};}
   if(action==='start'&&method==='POST'){
    if(!ai.ready)throw fault(503,'AI 尚未启用，请先配置 OpenAI API key。');
    if(!b.pages.length)throw fault(400,'请先上传扫描页。');
    if(b.pages.length!==b.expectedPages)throw fault(409,'扫描页尚未全部上传，请重新上传完整文件。');
    if(b.status==='starting')throw fault(409,'AI 请求仍在确认中，请稍后刷新。');
    const phase=input.phase==='grade'?'grade':'recognize';
    if(phase==='grade'&&!b.submissionIds.length)throw fault(400,'请先识别并转录原稿。');
    if(phase==='recognize'&&b.submissionIds.length)throw fault(409,'已有转录结果，请在作业内校正文字后重新批改。');
    return {batch:cleanBatch(await start(b,phase))};
   }
   if(action==='poll'&&method==='POST'){
    b=await poll(b);
    if(b.status==='transcribed'&&ai.ready)b=await start(b,'grade');
    return {batch:cleanBatch(b)};
   }
  }else{
   let s=await submission(id,user);
   if(!action&&method==='GET')return {submission:s};
   if(action==='pages'&&method==='GET'&&pageNumber){const p=Number(pageNumber);if(!s.pages.includes(p))throw fault(404,'扫描页不存在。');const b=await batch(s.batchId),page=await store.get('pages',b.pages[p-1]);return {page};}
   if(action==='publish'&&method==='POST'){
    requireTeacher(user);if(input.confirmed!==true||!/^\d{11}$/.test(input.studentId||''))throw fault(400,'请核对 11 位学号，并确认原稿归属与转录。');
    s=await mutate('submissions',id,async(current,tx)=>{const b=await tx.get('batches',current.batchId);if(['recognizing','grading','starting'].includes(b.status)||current.status!=='review')throw fault(409,'请先完成批改。');if(current.revision!==input.revision)throw fault(409,'作业已更新，请刷新后再发布。');return {...current,studentId:input.studentId,published:true,publishedAt:now(),revision:current.revision+1};});return {submission:s};
   }
   if(action==='edit'&&method==='POST'){
    requireTeacher(user);
    s=await mutate('submissions',id,async(current,tx)=>{
     const b=await tx.get('batches',current.batchId);if(['recognizing','grading','starting'].includes(b.status))throw fault(409,'请等待 AI 处理完成后再修改。');if(current.revision!==input.revision)throw fault(409,'作业已更新，请刷新后再修改。');
     if(input.blocks){
      if(!Array.isArray(input.blocks)||input.blocks.length!==current.blocks.length)throw fault(400,'转录段落数不匹配。');
      const blocks=current.blocks.map((original,i)=>{const edit=input.blocks[i];if(edit.id!==original.id||typeof edit.text!=='string'||edit.text.length>8000)throw fault(400,'转录格式无效。');return {...original,text:edit.text,uncertain:edit.uncertain===true};});
      return {...current,blocks,annotations:[],summary:'',status:'transcribed',published:false,revision:current.revision+1};
     }
     const valid=grades({submissions:[{id:current.id,summary:input.summary,annotations:input.annotations}]},[current])[0];
     return {...current,...valid,status:'review',published:false,revision:current.revision+1};
    });return {submission:s};
   }
  }
  throw fault(404,'接口不存在。');
 };
}
module.exports={createWorkspace,transcript,grades};
