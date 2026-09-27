import {authRequest,currentUser,openAccount} from './auth.js?v=20260927';
const root=document.createElement('main');root.id='homework-workspace';root.hidden=true;document.body.append(root);
const esc=value=>String(value??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const states={uploading:'待识别',starting:'正在启动',recognizing:'识别与转录',transcribed:'待批改',grading:'正在批改',review:'待教师复核',failed:'需要处理'};
const marks={correct:'✓',error:'×',suggestion:'△',uncertain:'?'};
let user=null,info=null,batches=[],submissions=[],selected=null,batch=null,view='scan',activeBlock='',loading=false,pollTimer=null,requestEpoch=0,nextBatch=null,nextSubmission=null;
const pageCache=new Map();
const $=s=>root.querySelector(s),$$=s=>[...root.querySelectorAll(s)];
const teacher=()=>user?.role==='teacher';
function status(text,error=false){const el=$('.work-status');if(el){el.textContent=text;el.classList.toggle('is-error',error);}}
async function run(work){if(loading)return;loading=true;root.setAttribute('aria-busy','true');try{await work();}catch(e){status(e.message,true);if(e.status===401)openAccount();}finally{loading=false;root.setAttribute('aria-busy','false');}}
const icon=name=>'<svg viewBox="0 0 48 48" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">'+{"upload":"<path d=\"M24 31V9m-8 8 8-8 8 8\"/><path d=\"M10 29v9a3 3 0 0 0 3 3h22a3 3 0 0 0 3-3v-9\"/>","library":"<rect x=\"9\" y=\"12\" width=\"24\" height=\"29\" rx=\"3\"/><path d=\"M16 12V7h23v28h-6M16 22h10m-10 7h10\"/>","settings":"<path d=\"M10 13h28M10 24h28M10 35h28\"/><circle cx=\"19\" cy=\"13\" r=\"4\"/><circle cx=\"31\" cy=\"24\" r=\"4\"/><circle cx=\"18\" cy=\"35\" r=\"4\"/>","refresh":"<path d=\"M38 19a15 15 0 1 0-1 14M38 9v10H28\"/>","home":"<rect x=\"10\" y=\"10\" width=\"10\" height=\"10\" rx=\"2\"/><rect x=\"28\" y=\"10\" width=\"10\" height=\"10\" rx=\"2\"/><rect x=\"10\" y=\"28\" width=\"10\" height=\"10\" rx=\"2\"/><rect x=\"28\" y=\"28\" width=\"10\" height=\"10\" rx=\"2\"/>"}[name]+'</svg>';
const iconButton=(id,name,label)=>`<button id="${id}" class="work-icon-button" type="button" aria-label="${label}" title="${label}">${icon(name)}</button>`;
function home(){clearTimeout(pollTimer);selected=null;batch=null;root.classList.remove('is-reading');empty();}
function reading(){root.classList.add('is-reading');$('#work-library').close();}
function frame(){
 root.innerHTML=`<header class="work-header"><a href="../" class="work-wordmark">阅见<span>作业系统</span></a><span class="work-role">${teacher()?'教师工作台':'我的作业'}</span></header><div class="work-shell"><nav class="work-launcher" aria-label="作业工具">${iconButton('work-home','home','返回工作台')}${teacher()?iconButton('work-upload','upload','上传扫描作业'):''}${iconButton('work-open-library','library',teacher()?'全部作业':'我的作业')}${teacher()?iconButton('work-settings','settings','AI 设置'):''}${iconButton('work-refresh','refresh','刷新')}</nav>${teacher()?'<input id="work-files" type="file" accept="application/pdf,image/jpeg,image/png,image/webp" multiple hidden>':''}<section class="work-main"><p class="work-status" role="status" aria-live="polite"></p><div id="work-content"></div></section></div><dialog id="work-library" aria-label="作业库"><button class="work-library-close" aria-label="关闭作业库">×</button><aside class="work-sidebar">${teacher()?'<h2>上传批次</h2><div id="work-batches"></div><button id="more-batches" hidden>加载更多批次</button>':''}<h2>${teacher()?'全部学生作业':'已发布的作业'}</h2><div id="work-submissions"></div><button id="more-submissions" hidden>加载更多作业</button></aside></dialog><dialog id="work-settings-dialog" aria-labelledby="work-settings-title"><button class="work-dialog-close" aria-label="关闭设置">×</button><h2 id="work-settings-title">AI 服务设置</h2><p>模型：GPT-6 Sol<br>推理档位：medium（中档）</p><form id="work-settings-form"><label>OpenAI API key<input name="key" type="password" autocomplete="off" placeholder="sk-…" required></label><label>你的作业系统密码<input name="password" type="password" autocomplete="current-password" required></label><p class="work-small">密钥仅发送给服务器并加密保存，不会在页面中回显。</p><button class="work-primary">验证并保存</button><p id="work-settings-status" role="status"></p></form></dialog>`;
 $('#work-refresh').onclick=()=>run(refresh);
 $('#work-home').onclick=home;$('#work-open-library').onclick=()=>$('#work-library').showModal();$('.work-library-close').onclick=()=>$('#work-library').close();
 $('#more-submissions').onclick=()=>run(async()=>{const r=await authRequest('/api/submissions?offset='+nextSubmission);submissions.push(...r.submissions);nextSubmission=r.nextOffset;lists();});
 if(teacher()){
  $('#work-upload').onclick=()=>$('#work-files').click();$('#work-files').onchange=event=>run(()=>upload([...event.target.files]));
  $('#more-batches').onclick=()=>run(async()=>{const r=await authRequest('/api/batches?offset='+nextBatch);batches.push(...r.batches);nextBatch=r.nextOffset;lists();});
  $('#work-settings').onclick=()=>$('#work-settings-dialog').showModal();
  $('.work-dialog-close').onclick=()=>$('#work-settings-dialog').close();
  $('#work-settings-form').onsubmit=async event=>{event.preventDefault();const form=event.currentTarget,button=form.querySelector('button');button.disabled=true;$('#work-settings-status').textContent='正在验证模型访问权限…';try{await authRequest('/api/settings/ai',{apiKey:form.elements.key.value,password:form.elements.password.value});form.reset();info=await authRequest('/api/workspace');$('#work-settings-status').textContent='已保存，AI 批改可以使用了。';lists();}catch(error){$('#work-settings-status').textContent=error.message;}finally{button.disabled=false;}};
  $('#work-settings-dialog').addEventListener('close',()=>$('#work-settings-form').reset());
 }
 empty();
}
function empty(){$('#work-content').innerHTML='';root.classList.remove('is-reading');}
function lists(){
 if(teacher()){
  $('#work-batches').innerHTML=batches.length?batches.map(b=>`<button class="work-list-item ${batch?.id===b.id?'selected':''}" data-batch="${esc(b.id)}"><strong>${esc(b.title)}</strong><span>${b.pages} 页 · ${esc(states[b.status]||b.status)}</span></button>`).join(''):'<p class="work-small">还没有上传。</p>';
  $('#work-settings').classList.toggle('needs-setup',!info?.aiReady);$('#work-settings').title=info?.aiReady?'AI 设置':'AI 设置 · 尚未配置';
  $('#more-batches').hidden=nextBatch===null;
  $$('[data-batch]').forEach(button=>button.onclick=()=>run(()=>selectBatch(button.dataset.batch)));
 }
 $('#work-submissions').innerHTML=submissions.length?submissions.map(s=>`<button class="work-list-item ${selected?.id===s.id?'selected':''}" data-submission="${esc(s.id)}"><strong>${esc(s.title)}</strong><span>${teacher()?esc(s.name||'待核对')+' · '+esc(s.studentId||'学号待核对')+'<br>':''}${s.pages} 页${teacher()?' · '+(s.published?'已发布':'草稿'):''}</span></button>`).join(''):'<p class="work-small">暂无可查看的作业。</p>';
 $('#more-submissions').hidden=nextSubmission===null;
 $$('[data-submission]').forEach(button=>button.onclick=()=>run(()=>selectSubmission(button.dataset.submission)));
}
async function refresh(){
 const epoch=requestEpoch;status('正在连接服务器…');
 const results=await Promise.all([authRequest('/api/workspace'),authRequest('/api/submissions'),...(teacher()?[authRequest('/api/batches')]:[])]);
 if(epoch!==requestEpoch)return;
 info=results[0];submissions=results[1].submissions;nextSubmission=results[1].nextOffset;
 if(teacher()){batches=results[2].batches;nextBatch=results[2].nextOffset;}
 lists();status('');

}
function monitor(b){
 const usage=(b.usage||[]).reduce((total,u)=>({input:total.input+(u.input_tokens||0),output:total.output+(u.output_tokens||0),reasoning:total.reasoning+(u.output_tokens_details?.reasoning_tokens||0),cached:total.cached+(u.input_tokens_details?.cached_tokens||0)}),{input:0,output:0,reasoning:0,cached:0});
 return `<header class="work-document-header"><div><p class="work-eyebrow">${esc(states[b.status]||b.status)}</p><h2>${esc(b.title)}</h2><p>${b.pages.length} 页 · GPT-6 Sol · medium</p></div>${['uploading','failed'].includes(b.status)&&!b.submissionIds.length?'<button class="work-primary" id="work-start">开始识别与批改</button>':''}${b.submissionIds.length&&!['starting','recognizing','grading'].includes(b.status)?'<button id="work-regrade" class="work-secondary">重新批改</button>':''}</header><div class="work-monitor"><div class="work-metrics"><div><small>已结算输入 token</small><strong>${usage.input.toLocaleString()}</strong></div><div><small>已结算输出 token</small><strong>${usage.output.toLocaleString()}</strong></div><div><small>其中推理 token</small><strong>${usage.reasoning.toLocaleString()}</strong></div><div><small>缓存输入 token</small><strong>${usage.cached.toLocaleString()}</strong></div></div><p class="work-small">每阶段结束后显示 API 返回的实际用量；处理中的 token 尚未结算。</p><ol class="work-events">${(b.events||[]).map(e=>`<li><time>${new Date(e.at).toLocaleTimeString('zh-CN')}</time>${esc(e.message)}</li>`).join('')}</ol>${b.error?`<p class="work-error">${esc(b.error)}</p>`:''}${b.ai?.liveText?`<details class="work-live" open><summary>正在生成的转录 / 批改输出</summary><pre>${esc(b.ai.liveText.slice(-7000))}</pre></details>`:''}</div>${b.submissionIds.length?'<p class="work-review-note">请从作业库选择学生作业，核对学号、原稿和批注后发布。未发布的作业只对教师可见。</p>':''}<div id="work-batch-pages" class="work-page-thumbnails"></div>`;
}
async function selectBatch(id){
 clearTimeout(pollTimer);selected=null;const data=await authRequest('/api/batches/'+id);batch=data.batch;reading();$('#work-content').innerHTML=monitor(batch);bindMonitor();lists();await batchThumbnails();schedulePoll();
}
function bindMonitor(){if($('#work-start'))$('#work-start').onclick=()=>run(async()=>{const r=await authRequest('/api/batches/'+batch.id+'/start',{phase:'recognize'});batch=r.batch;$('#work-content').innerHTML=monitor(batch);bindMonitor();schedulePoll();});if($('#work-regrade'))$('#work-regrade').onclick=()=>run(async()=>{const r=await authRequest('/api/batches/'+batch.id+'/start',{phase:'grade'});batch=r.batch;$('#work-content').innerHTML=monitor(batch);bindMonitor();schedulePoll();});}
async function batchThumbnails(){const current=batch;if(!current)return;for(let i=1;i<=current.pages.length;i++){const page=await imagePage('batches',current.id,i);if(batch?.id!==current.id||selected)return;const img=document.createElement('img');img.src=page;img.alt='扫描页 '+i;$('#work-batch-pages')?.append(img);}}
function schedulePoll(){clearTimeout(pollTimer);if(!batch||!['starting','recognizing','grading','transcribed'].includes(batch.status)||selected)return;pollTimer=setTimeout(async()=>{if(document.hidden){schedulePoll();return;}try{const id=batch.id,epoch=requestEpoch,r=await authRequest('/api/batches/'+id+'/poll',{});if(epoch!==requestEpoch||batch?.id!==id||selected)return;batch=r.batch;$('#work-content').innerHTML=monitor(batch);bindMonitor();if(['review','failed'].includes(batch.status))await refresh();else{const entry=batches.find(b=>b.id===id);if(entry)entry.status=batch.status;lists();}}catch(error){status(error.message,true);}schedulePoll();},2200);}
async function imagePage(kind,id,number){const key=kind+id+number;if(pageCache.has(key))return pageCache.get(key);const {page}=await authRequest('/api/'+kind+'/'+id+'/pages/'+number);const url='data:image/jpeg;base64,'+page.data;pageCache.set(key,url);return url;}
function math(container){if(!window.katex)return;for(const el of container.querySelectorAll('[data-math]')){const raw=el.textContent;el.textContent='';let at=0;const regex=/\\\[([\s\S]*?)\\\]|\\\(([\s\S]*?)\\\)/g;for(const match of raw.matchAll(regex)){el.append(document.createTextNode(raw.slice(at,match.index)));const span=document.createElement('span');try{window.katex.render(match[1]??match[2],span,{displayMode:match[1]!==undefined,throwOnError:false,trust:false,strict:'ignore'});}catch{span.textContent=match[0];}el.append(span);at=match.index+match[0].length;}el.append(document.createTextNode(raw.slice(at)));}}
async function selectSubmission(id){clearTimeout(pollTimer);batch=null;selected=(await authRequest('/api/submissions/'+id)).submission;activeBlock='';reading();renderSubmission();lists();await showPages();}
function renderSubmission(){
 const s=selected;
 $('#work-content').innerHTML=`<header class="work-document-header"><div><p class="work-eyebrow">${s.published?'已发布':'教师复核 · 尚未发布'}</p><h2>${esc(s.title)}</h2><p>${esc(s.name)} ${esc(s.studentId||'学号待核对')} · ${s.pages.length} 页</p></div><button id="work-print" class="work-secondary">打印当前版本</button></header><div class="work-view-tabs" role="group" aria-label="作业版本"><button data-view="scan" aria-pressed="${view==='scan'}">扫描版</button><button data-view="typed" aria-pressed="${view==='typed'}">电脑字体版</button><span>同一份批注 · 不评分</span></div><div class="work-reading"><div id="work-pages"></div><aside class="work-feedback"><h3>批改意见</h3><p class="work-summary" data-math>${esc(s.summary||'等待批改。')}</p>${s.annotations.map((a,i)=>`<button class="work-comment ${esc(a.kind)}" data-block="${esc(a.blockId)}"><span class="work-mark">${marks[a.kind]}</span><span><b>${i+1}</b><span data-math>${esc(a.comment)}</span>${a.correction?`<small data-math>${esc(a.correction)}</small>`:''}</span></button>`).join('')||'<p class="work-small">暂无批注。</p>'}</aside></div>${teacher()?`<section class="work-review"><h3>教师复核</h3><p class="work-small">电脑字体版应忠实保留原稿，包括学生的错误。模糊内容请核对扫描页。</p><div class="work-review-actions"><button id="work-edit-text" class="work-secondary">校正转录文字</button><button id="work-edit-feedback" class="work-secondary">修改批注</button><button id="work-show-batch" class="work-secondary">查看 AI 过程 / 重新批改</button></div><div id="work-editor"></div><form id="work-publish"><label>作业所属学号<input name="studentId" inputmode="numeric" pattern="[0-9]{11}" maxlength="11" value="${esc(s.studentId)}" placeholder="11 位学号" required></label><label class="work-checkbox"><input name="confirmed" type="checkbox" required>已核对学号、扫描页归属、转录内容及批注</label><button class="work-primary" ${s.status!=='review'?'disabled':''}>${s.published?'更新发布':'发布给该学生'}</button></form></section>`:''}`;
 $$('[data-view]').forEach(button=>button.onclick=()=>{view=button.dataset.view;renderSubmission();showPages().catch(e=>status(e.message,true));});
 $$('[data-block]').forEach(button=>button.onclick=()=>focusBlock(button.dataset.block));
 $('#work-print').onclick=()=>window.print();
 if(teacher()){
  $('#work-show-batch').onclick=()=>run(()=>selectBatch(s.batchId));
  $('#work-edit-text').onclick=()=>editText();$('#work-edit-feedback').onclick=()=>editFeedback();
  $('#work-publish').onsubmit=event=>{event.preventDefault();const form=event.currentTarget;run(async()=>{const r=await authRequest('/api/submissions/'+s.id+'/publish',{studentId:form.elements.studentId.value,confirmed:form.elements.confirmed.checked,revision:s.revision});selected=r.submission;renderSubmission();await showPages();await refresh();status('已发布。只有该学号登录后可以查看。');});};
 }
 math($('#work-content'));
}
async function showPages(){
 const s=selected;if(!s)return;const container=$('#work-pages');
 container.innerHTML=s.pages.map(number=>`<article class="work-page" data-page="${number}"><div class="work-page-label">第 ${number} 页</div>${view==='scan'?`<div class="work-scan"><img alt="学生作业扫描页 ${number}">${s.annotations.map((a,i)=>{const b=s.blocks.find(b=>b.id===a.blockId);if(b?.page!==number)return '';const [x,y,w,h]=b.bbox;return `<button class="work-scan-mark ${esc(a.kind)}" data-block="${esc(b.id)}" aria-label="批注 ${i+1}：${esc(a.comment)}" style="left:${x*100}%;top:${y*100}%;width:${w*100}%;height:${h*100}%"><span>${marks[a.kind]} ${i+1}</span></button>`;}).join('')}</div>`:`<div class="work-typed">${s.blocks.filter(b=>b.page===number).map(b=>`<div class="work-text-block ${b.uncertain?'uncertain':''}" id="block-${esc(b.id)}" data-text-block="${esc(b.id)}"><p data-math>${esc(b.text)}</p>${b.uncertain?'<small>原文待核对</small>':''}<div class="work-inline-marks">${s.annotations.map((a,i)=>a.blockId===b.id?`<button class="${esc(a.kind)}" data-block="${esc(b.id)}" aria-label="批注 ${i+1}">${marks[a.kind]} ${i+1}</button>`:'').join('')}</div></div>`).join('')}</div>`}</article>`).join('');
 container.querySelectorAll('[data-block]').forEach(button=>button.onclick=()=>focusBlock(button.dataset.block));math(container);
 if(view==='scan')for(const number of s.pages){const url=await imagePage('submissions',s.id,number);if(selected?.id!==s.id||view!=='scan')return;const image=$(`[data-page="${number}"] img`);if(image)image.src=url;}
}
function focusBlock(id){activeBlock=id;$$('[data-block],[data-text-block]').forEach(el=>el.classList.toggle('active',(el.dataset.block||el.dataset.textBlock)===id));const target=$$('[data-text-block],.work-scan-mark').find(el=>(el.dataset.block||el.dataset.textBlock)===id);target?.scrollIntoView({behavior:'smooth',block:'center'});}
function editText(){
 const s=selected;$('#work-editor').innerHTML=`<form id="work-text-form"><p class="work-small">只校正识别错误。保存会撤下已发布版本并清除旧批注，之后请重新批改。</p>${s.blocks.map((b,i)=>`<label>第 ${b.page} 页 · 段落 ${i+1}<textarea name="text${i}">${esc(b.text)}</textarea></label><label class="work-checkbox"><input type="checkbox" name="uncertain${i}" ${b.uncertain?'checked':''}>仍有无法辨认之处</label>`).join('')}<button class="work-primary">保存转录</button></form>`;
 $('#work-text-form').onsubmit=event=>{event.preventDefault();const form=event.currentTarget;run(async()=>{const blocks=s.blocks.map((b,i)=>({id:b.id,text:form.elements['text'+i].value,uncertain:form.elements['uncertain'+i].checked}));selected=(await authRequest('/api/submissions/'+s.id+'/edit',{revision:s.revision,blocks})).submission;renderSubmission();await showPages();status('转录已保存，请重新批改后发布。');});};
}
function editFeedback(){
 const s=selected;$('#work-editor').innerHTML=`<form id="work-feedback-form"><label>总体意见<textarea name="summary">${esc(s.summary)}</textarea></label>${s.annotations.map((a,i)=>`<fieldset><legend>批注 ${i+1}</legend><label>标记<select name="kind${i}">${Object.entries({correct:'正确',error:'错误',suggestion:'建议',uncertain:'待核对'}).map(([v,t])=>`<option value="${v}" ${a.kind===v?'selected':''}>${t}</option>`).join('')}</select></label><label>意见<textarea name="comment${i}">${esc(a.comment)}</textarea></label><label>修正建议<textarea name="correction${i}">${esc(a.correction)}</textarea></label></fieldset>`).join('')}<button class="work-primary">保存批注</button></form>`;
 $('#work-feedback-form').onsubmit=event=>{event.preventDefault();const form=event.currentTarget;run(async()=>{const annotations=s.annotations.map((a,i)=>({...a,kind:form.elements['kind'+i].value,comment:form.elements['comment'+i].value,correction:form.elements['correction'+i].value}));selected=(await authRequest('/api/submissions/'+s.id+'/edit',{revision:s.revision,summary:form.elements.summary.value,annotations})).submission;renderSubmission();await showPages();status('批注已同步到两个版本，请核对后发布。');});};
}
async function jpeg(canvas){
 let quality=.88,data=canvas.toDataURL('image/jpeg',quality).split(',')[1];
 while(data.length>630000&&quality>.45){quality-=.1;data=canvas.toDataURL('image/jpeg',quality).split(',')[1];}
 if(data.length>630000)throw new Error('该页图像过大，请将扫描分辨率调低后再试。');
 return {data,width:canvas.width,height:canvas.height};
}
async function* scanPages(files){
 let count=0;
 for(const file of files){
  if(file.size>30*1024*1024)throw new Error('单个文件请控制在 30 MB 以内。');
  if(file.type==='application/pdf'||file.name.toLowerCase().endsWith('.pdf')){
   const pdfjs=await import('./vendor/pdf.mjs');pdfjs.GlobalWorkerOptions.workerSrc=new URL('./vendor/pdf.worker.mjs',import.meta.url).href;
   const pdf=await pdfjs.getDocument({data:new Uint8Array(await file.arrayBuffer()),isEvalSupported:false,enableXfa:false}).promise;
   try{if(count+pdf.numPages>20)throw new Error('每批最多 20 页，请拆分文件后上传。');
    for(let p=1;p<=pdf.numPages;p++){const page=await pdf.getPage(p),base=page.getViewport({scale:1}),viewport=page.getViewport({scale:1800/Math.max(base.width,base.height)}),canvas=document.createElement('canvas');canvas.width=Math.ceil(viewport.width);canvas.height=Math.ceil(viewport.height);await page.render({canvasContext:canvas.getContext('2d'),viewport}).promise;count++;yield await jpeg(canvas);page.cleanup();}
   }finally{await pdf.destroy();}
  }else{
   if(!['image/jpeg','image/png','image/webp'].includes(file.type))throw new Error('请选择 PDF、JPEG、PNG 或 WebP 文件。');
   if(++count>20)throw new Error('每批最多 20 页。');const bitmap=await createImageBitmap(file);
   try{const scale=Math.min(1,1800/Math.max(bitmap.width,bitmap.height)),canvas=document.createElement('canvas');canvas.width=Math.round(bitmap.width*scale);canvas.height=Math.round(bitmap.height*scale);const ctx=canvas.getContext('2d');ctx.fillStyle='white';ctx.fillRect(0,0,canvas.width,canvas.height);ctx.drawImage(bitmap,0,0,canvas.width,canvas.height);yield await jpeg(canvas);}finally{bitmap.close();}
  }
 }
}
async function upload(files){
 if(!files.length)return;const title=files.length===1?files[0].name.replace(/\.[^.]+$/,''):new Date().toLocaleDateString('zh-CN')+' 作业';
 status('正在读取扫描件…');const prepared=[];for await(const page of scanPages(files)){prepared.push(page);status('已整理 '+prepared.length+' 页，正在读取…');}
 const data=await authRequest('/api/batches',{title:title.slice(0,100),expectedPages:prepared.length});const id=data.batch.id;
 for(let i=0;i<prepared.length;i++){status('正在安全上传第 '+(i+1)+' / '+prepared.length+' 页…');await authRequest('/api/batches/'+id+'/pages',{...prepared[i],number:i+1});}
 await refresh();await selectBatch(id);status(info.aiReady?'上传完成，点击“开始识别与批改”。':'上传已保存。请先配置 API key，再开始 AI 识别。');$('#work-files').value='';
}
async function changeUser(next){
 if(user?.studentId===next?.studentId&&user?.role===next?.role)return;
 requestEpoch++;clearTimeout(pollTimer);pageCache.clear();user=next;selected=null;batch=null;submissions=[];batches=[];info=null;loading=false;
 root.hidden=!user;document.body.classList.toggle('has-homework-session',Boolean(user));
 root.classList.remove('is-reading');if(user){frame();await run(refresh);}else root.innerHTML='';
}
window.addEventListener('homework-auth-change',event=>changeUser(event.detail));
document.addEventListener('keydown',event=>{if(!root.hidden&&event.target.closest('#homework-workspace'))event.stopPropagation();},true);
changeUser(currentUser());
