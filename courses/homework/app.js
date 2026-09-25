import {renderNotebook} from './notebook.js';
import {getDemoQuestion,getDemoGrade} from './demo-grader.js';
const $=(s,root=document)=>root.querySelector(s), $$=(s,root=document)=>[...root.querySelectorAll(s)];
const esc=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const students=[{name:'林同学',id:'20260018'},{name:'陈同学',id:'20260023'},{name:'周同学',id:'20260031'}];
const subjects={university:'大学数学',secondary:'中学数学',general:'通用作业'};
const panelFonts={sans:'简洁体',song:'宋体',hand:'手写体'};
const paperBackgrounds={plain:'空白',ruled:'横线本',grid:'方格本',tian:'田字格'};
const documentStyles={exam:'试卷',notebook:'作业本'};
const readingModes={single:'单页',double:'双页'};
const icon=body=>`<svg viewBox="0 0 24 24" aria-hidden="true" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round">${body}</svg>`;
const icons={settings:icon('<path d="m9 3-.7 2.3-2.2 1L4 5.7l-2 3.5 1.7 1.6v2.5L2 14.8l2 3.5 2.1-.6 2.2 1L9 21h4l.7-2.3 2.2-1 2.1.6 2-3.5-1.7-1.5v-2.5L20 9.2l-2-3.5-2.1.6-2.2-1L13 3Z"/><circle cx="11" cy="12" r="3"/>'),zoom:icon('<path d="M8 3H3v5m13-5h5v5M3 16v5h5m13-5v5h-5"/>'),marks:icon('<path d="M2 12s4-7 10-7 10 7 10 7-4 7-10 7-10-7-10-7Z"/><circle cx="12" cy="12" r="3"/><path class="eye-off" d="m3 3 18 18"/>'),single:icon('<path d="M6 3h12v18H6zM9 8h6m-6 4h6m-6 4h4"/>'),double:icon('<path d="M2 4h9v16H2zM13 4h9v16h-9zM5 9h3m-3 4h3m8-4h3m-3 4h3"/>')};
const pens={'#af4b45':'朱批','#476d8f':'蓝墨','#595b60':'石墨'};
const presets={studio:{name:'清朗',ink:'#af4b45'},pro:{name:'石墨',ink:'#595b60'},paper:{name:'纸感',ink:'#af4b45'}};
const key='yuejian-paper-preferences-v3';
let storageOK=true;
function read(){try{return JSON.parse(localStorage.getItem(key))||{}}catch{storageOK=false;return {}}}
const stored=read();
function sanitize(v={}){const p=Object.hasOwn(presets,v.preset)?v.preset:'studio',base=presets[p],documentStyle='notebook';return {documentStyle,panelFont:Object.hasOwn(panelFonts,v.panelFont)?v.panelFont:'sans',background:Object.hasOwn(paperBackgrounds,v.background)?v.background:(documentStyle==='notebook'?'ruled':'plain'),reading:v.documentStyle!=='exam'&&Object.hasOwn(readingModes,v.reading)?v.reading:'double',preset:p,ink:Object.hasOwn(pens,v.ink)?v.ink:base.ink,marks:typeof v.marks==='boolean'?v.marks:true,subject:Object.hasOwn(subjects,v.subject)?v.subject:'university'}}
let settings=sanitize(stored.notebookDefaults?stored.settings:{...stored.settings,documentStyle:'notebook',reading:'double'}),candidates=Array.isArray(stored.candidates)?stored.candidates.slice(0,4).map(c=>({id:String(c.id),settings:sanitize(c.settings)})):[];
let note=typeof stored.note==='string'?stored.note:'',confirmed=stored.confirmed||null;
let student=0,active=0,zoom=false,prefsOpen=false;
let settingsObserver;
let bookPage=0,turnAnimation=null,turnStage=null;
const records={};
const record=i=>{const id=[settings.subject,student,i].join('-');return records[id]||(records[id]=getDemoGrade(settings.subject,student,i))};
const questions=()=>[getDemoQuestion(settings.subject,student,0),getDemoQuestion(settings.subject,student,1)];
function persist(){try{localStorage.setItem(key,JSON.stringify({settings,candidates,note,confirmed,notebookDefaults:1}));storageOK=true}catch{storageOK=false}return storageOK}
function announce(text,i=active){const s=$('#status');if(s)s.textContent=text;const near=$('[data-confirm-state="'+i+'"]');if(near)near.textContent=text}
function prefMarkup(){return `<section class="paper-preferences" id="preferences" ${prefsOpen?'':'hidden'} aria-label="设置"><div class="preference-heading"><strong>设置</strong><button data-action="close-preferences" aria-label="关闭设置">收起 ↑</button></div><fieldset class="document-style-settings"><legend>文稿样式</legend><div class="document-style-options">${Object.entries(documentStyles).map(([id,name])=>`<label class="document-style-option"><input type="radio" name="document-style" value="${id}" ${id==='exam'?'disabled aria-label="试卷（暂未开放）"':''} ${settings.documentStyle===id?'checked':''}><span class="style-preview style-preview-${id}" aria-hidden="true"><i></i><i></i></span><span>${name}${id==='exam'?'<small>暂未开放</small>':''}</span></label>`).join('')}</div></fieldset><fieldset class="reading-settings"><legend>阅览方式</legend><div class="reading-options">${Object.entries(readingModes).map(([id,name])=>`<label class="reading-option"><input type="radio" name="reading" value="${id}" ${settings.reading===id?'checked':''}><span>${icons[id]}${name}</span></label>`).join('')}</div><p class="reading-hint">${settings.reading==='double'?'双页并排，按原稿顺序连续阅读。':'单页居中，向下连续阅读。'}</p><p class="narrow-reading-hint" ${settings.reading==='double'?'':'hidden'}>纸张比例固定，窗口只改变整体显示倍率。</p></fieldset><fieldset class="paper-background-settings"><legend>作业背景</legend><div class="background-options">${Object.entries(paperBackgrounds).map(([id,name])=>`<label class="background-option"><input type="radio" name="background" value="${id}" ${settings.background===id?'checked':''}><span class="paper-sample" data-paper="${id}" aria-hidden="true"></span><span>${name}</span></label>`).join('')}</div></fieldset><label class="pref-field panel-font-field">设置字体<select id="panel-font">${Object.entries(panelFonts).map(([id,name])=>`<option value="${id}" ${settings.panelFont===id?'selected':''}>${name}</option>`).join('')}</select></label><div class="preset-options" role="group" aria-label="外观方案">${Object.entries(presets).map(([id,p])=>`<button data-preset="${id}" aria-pressed="${id===settings.preset}">${p.name}</button>`).join('')}</div><div class="preference-controls"><div class="pref-field"><span>批注用墨</span><div class="pen-colors" role="group" aria-label="批注颜色">${Object.entries(pens).map(([color,name])=>`<button style="color:${color}" data-ink="${color}" aria-label="${name}" aria-pressed="${settings.ink===color}" title="${name}">✓</button>`).join('')}</div></div><label class="pref-field">示例学科<select id="subject">${Object.entries(subjects).map(([id,name])=>`<option value="${id}" ${id===settings.subject?'selected':''}>${name}</option>`).join('')}</select></label><button data-action="toggle-marks" id="marks-setting">${settings.marks?'隐藏批注':'显示批注'}</button></div><div class="preference-actions"><button data-action="confirm-choice">选定此版</button><button data-action="save-candidate" id="save-candidate">保留一个候选</button><button data-action="reset-style">恢复默认</button></div><div id="candidate-list" class="candidate-list"></div><p class="preference-help">仅保存在当前浏览器。选定后可复制偏好给我。</p><section id="choice-section" class="choice-section" hidden><label for="preference-note">还想怎样调整？</label><textarea id="preference-note" placeholder="例如：批注更贴近答案，或分数再小一些。">${esc(note)}</textarea><div class="preference-actions"><button data-action="copy-choice">复制偏好</button><button data-action="download-choice">下载偏好</button></div><textarea readonly id="preference-summary" class="preference-summary" aria-label="可复制的设计偏好"></textarea><p class="preference-help">复制后粘贴到对话中；这里不会自动发送。</p></section></section>`}
function render(){const s=students[student];const qs=questions();
 const tools=`<div class="paper-tools"><div class="paper-identity"><a class="wordmark" href="../" aria-label="返回课程主页">阅见</a><span>原稿演示</span><span class="paper-progress" data-progress></span></div></div>`;
 $('#workspace-tools').innerHTML=`<div class="paper-controls"><button data-action="previous-student" aria-label="上一位学生" ${student===0?'disabled':''}>‹</button><span class="student-label">${s.name} ${student+1}/3</span><button data-action="next-student" aria-label="下一位学生" ${student===2?'disabled':''}>›</button><div class="reading-tools" role="group" aria-label="阅览工具"><button class="icon-button" data-action="toggle-zoom" id="zoom" aria-label="放大原稿" aria-pressed="${zoom}" data-tip="放大原稿">${icons.zoom}</button><button class="icon-button" data-action="toggle-marks" id="marks" aria-label="隐藏批注" aria-pressed="${settings.marks}" data-tip="隐藏批注">${icons.marks}</button><button class="icon-button" data-action="preferences" aria-label="设置" aria-controls="preferences" aria-expanded="${prefsOpen}" data-tip="设置">${icons.settings}</button></div></div>`;
 $('#settings-root').innerHTML=prefMarkup();
 settingsObserver?.disconnect();settingsObserver=new ResizeObserver(syncSettingsMask);settingsObserver.observe($('#preferences'));
 $('#manuscript').innerHTML=renderNotebook({questions:qs,student:{...s,correct:student===1&&settings.subject!=='general'},grades:[record(0),record(1)],tools});
 bind();apply();refreshGrade(0);refreshGrade(1);selectQuestion(active);renderCandidates();sizeNotes();
}
function apply(){cancelPageTurn();const root=$('#manuscript');document.documentElement.style.setProperty('--ink',settings.ink);document.documentElement.dataset.panelFont=settings.panelFont;root.dataset.paper=settings.background;root.dataset.documentStyle=settings.documentStyle;$$('input[name=document-style]').forEach(el=>el.checked=el.value===settings.documentStyle);$$('[data-document-kind]').forEach(el=>el.textContent=documentStyles[settings.documentStyle]);$('#panel-font').value=settings.panelFont;$$('input[name=background]').forEach(el=>el.checked=el.value===settings.background);root.style.setProperty('--ink',settings.ink);root.style.setProperty('--paper',settings.documentStyle==='notebook'?'#fffef9':(settings.preset==='paper'?'#fffef8':'#fff')); root.classList.toggle('no-marks',!settings.marks);root.classList.toggle('zoomed',zoom);root.dataset.reading=settings.reading;$$('input[name=reading]').forEach(el=>el.checked=el.value===settings.reading);$('.reading-hint').textContent=settings.reading==='double'?(settings.documentStyle==='notebook'?'左右对页，用纸页下方的箭头翻页。':'两张试卷并排，按原稿顺序连续阅读。'):(settings.documentStyle==='notebook'?'每次一页，用纸页下方的箭头翻页。':'单页居中，向下连续阅读。');$('.narrow-reading-hint').hidden=true;$$('[data-preset]').forEach(b=>b.setAttribute('aria-pressed',b.dataset.preset===settings.preset));$$('[data-ink]').forEach(b=>b.setAttribute('aria-pressed',b.dataset.ink===settings.ink));for(const [id,label,pressed] of [['marks',settings.marks?'隐藏批注':'显示批注',settings.marks],['zoom',zoom?'还原大小':'放大原稿',zoom]]){const b=$('#'+id);b.setAttribute('aria-label',label);b.setAttribute('aria-pressed',pressed);b.dataset.tip=label;}if($('#marks-setting'))$('#marks-setting').textContent=settings.marks?'隐藏批注':'显示批注';syncBookView();fitPaper();sizeNotes();scheduleSettingsMask();persist()}
function selectQuestion(i){active=i;$$('[data-question-region]').forEach(r=>r.dataset.active=String(Number(r.dataset.questionRegion)===i))}
function sizeNotes(){$$('.ink-comment').forEach(t=>{t.style.height='auto';t.style.height=Math.max(36,t.scrollHeight)+'px'})}
const bookStep=()=>settings.reading==='double'?2:1;
function syncBookView(){
 const notebook=settings.documentStyle==='notebook',step=bookStep();
 const pages=$$('[data-page-number]');bookPage=Math.max(0,Math.min(bookPage,pages.length));
 const cover=notebook&&bookPage===0;
 const start=step===2?Math.floor((Math.max(1,bookPage)-1)/2)*2+1:Math.max(1,bookPage);
 $$('.page-spread').forEach(spread=>spread.hidden=spread.classList.contains('cover-spread')?!cover:cover||(notebook&&!$$('[data-page-number]',spread).some(p=>Number(p.dataset.pageNumber)>=start&&Number(p.dataset.pageNumber)<start+step)));
 pages.forEach(page=>page.hidden=cover||(notebook&&(Number(page.dataset.pageNumber)<start||Number(page.dataset.pageNumber)>=start+step)));
 $$('[data-turn]').forEach(b=>{b.disabled=Number(b.dataset.turn)<0?cover:!cover&&start+step>pages.length;if(b.classList.contains('book-previous'))b.textContent=start===1?'← 封面':'← 上一页'});
 $$('[data-jump-end]').forEach(b=>b.textContent=notebook?'核对续答 →':'核对续页 ↘');
 $('#manuscript').dataset.visiblePages=cover?'cover':notebook?(step===2&&start<pages.length?start+'–'+Math.min(start+1,pages.length):String(start)):'all';
}

function cancelPageTurn(){turnAnimation?.cancel();turnAnimation=null;turnStage?.remove();turnStage=null}
const snapshotProperties=('box-sizing display position top right bottom left width height min-width min-height max-width max-height padding margin gap border border-radius background background-image background-size box-shadow color font-family font-size font-weight font-style line-height letter-spacing text-align text-decoration white-space word-break overflow-wrap align-items justify-content flex flex-direction flex-wrap flex-shrink grid-template-columns transform transform-origin opacity z-index overflow vertical-align appearance isolation visibility').split(' ');
function captureLeaf(leaf){
 if(!leaf)return null;
 const rect=leaf.getBoundingClientRect(),copy=leaf.cloneNode(true);
 const originals=[leaf,...leaf.querySelectorAll('*')],copies=[copy,...copy.querySelectorAll('*')];
 originals.forEach((source,i)=>{const target=copies[i],style=getComputedStyle(source);target.style.cssText=snapshotProperties.concat(Array.from(style).filter(k=>k.startsWith('--'))).map(k=>k+':'+style.getPropertyValue(k)).join(';');for(const attr of [...target.attributes])if(['id','for','aria-labelledby','aria-describedby','name'].includes(attr.name)||attr.name.startsWith('data-'))target.removeAttribute(attr.name);if('value' in source)target.value=source.value;target.removeAttribute('autofocus')});
 // Keep the clone at native paper coordinates, then scale its entire surface.
 // Resizing only its outer box would reflow text during the page-turn animation.
 Object.assign(copy.style,{position:'absolute',left:'0',top:'0',width:leaf.offsetWidth+'px',height:leaf.offsetHeight+'px',margin:'0',transform:`scale(${rect.width/leaf.offsetWidth},${rect.height/leaf.offsetHeight})`,transformOrigin:'0 0',zoom:'1',pointerEvents:'none'});
 const snapshot=document.createElement('div');snapshot.className='turn-leaf-snapshot';
 Object.assign(snapshot.style,{position:'absolute',left:rect.left+'px',top:rect.top+'px',width:rect.width+'px',height:rect.height+'px',pointerEvents:'none'});
 snapshot.append(copy);snapshot.inert=true;snapshot.setAttribute('aria-hidden','true');return snapshot;
}

// A flexible leaf is drawn as joined vertical bands. The reverse side carries
// the destination page, while the old facing page stays beneath it until covered.
function animateBookTurn(front,back,stationary,rect,forward,openingSpread=null){
 const stage=document.createElement('div');stage.className='page-turn-stage';stage.inert=true;stage.setAttribute('aria-hidden','true');
 if(stationary)stage.append(stationary);
 const shadow=document.createElement('div');shadow.className='turn-contact-shadow';
 Object.assign(shadow.style,{left:rect.left+'px',top:rect.top+'px',width:rect.width+'px',height:rect.height+'px',background:`linear-gradient(${forward?'90deg':'270deg'},rgba(40,37,25,.24),transparent 75%)`});stage.append(shadow);
 const scene=document.createElement('div');scene.className='page-turn-scene';
 const pivot=forward?rect.left:rect.right,direction=forward?1:-1,w=rect.width,h=rect.height,count=16,bandWidth=w/count;
 scene.style.perspectiveOrigin=pivot+'px '+(rect.top+h/2)+'px';stage.append(scene);
 const bands=[];
 for(let i=0;i<count;i++){
  const band=document.createElement('div');band.className='turn-band';band.style.width=bandWidth+'px';band.style.height=h+'px';
  for(const [source,isBack] of [[front,false],[back,true]]){
   const face=document.createElement('div');face.className='turn-face'+(isBack?' turn-face-back':'');face.style.width=(bandWidth+.6)+'px';face.style.transformOrigin=(bandWidth/2)+'px 50%';
   const copy=source.cloneNode(true),offset=(forward!==isBack)?i*bandWidth:w-(i+1)*bandWidth;
   Object.assign(copy.style,{left:-offset+'px',top:'0',width:w+'px',height:h+'px',boxShadow:'none'});face.append(copy);
   const shade=document.createElement('div');shade.className='turn-shading';face.append(shade);band.append(face);
  }
  scene.append(band);bands.push(band);
 }
 const landing=back.cloneNode(true);landing.classList.add('turn-landing');landing.style.opacity='0';stage.append(landing);
 // Keep the destination's empty left half empty until the cover has landed.
 // Clip the whole spread, including its paper, binding and outer shadows.
 openingSpread?.classList.add('cover-opening');
 const revealSpread=()=>openingSpread?.classList.remove('cover-opening');
 document.body.append(stage);turnStage=stage;
 let frame=0,startTime;
 const handle={cancel(){cancelAnimationFrame(frame);revealSpread()}};turnAnimation=handle;
 function draw(now){
  if(startTime===undefined)startTime=now;
  const t=Math.min(1,(now-startTime)/1020),motion=Math.min(1,t/.84),progress=(1-Math.cos(Math.PI*motion))/2;
  const wave=motion===1?0:Math.sin(Math.PI*progress);
  const bend=.9*wave,base=Math.PI*progress;
  let x=0,z=0;
  for(let i=0;i<count;i++){
   const u=(i+.5)/count,angle=base+bend*(u-.5);
   const dx=motion===1?-bandWidth:bandWidth*Math.cos(angle),dz=motion===1?0:bandWidth*Math.sin(angle);
   const lift=-7*wave*u*u;
   bands[i].style.transform=`translate3d(${pivot+direction*(x+dx/2)-bandWidth/2}px,${rect.top+lift}px,${z+dz/2}px) rotateY(${-direction*angle}rad)`;
   bands[i].style.setProperty('--shade',String(wave*(.05+.12*u)));
   x+=dx;z+=dz;
  }
  shadow.style.opacity=String(wave*.65);
  shadow.style.transform=`scaleX(${.45+.55*Math.abs(Math.cos(base))})`;
  shadow.style.transformOrigin=forward?'left':'right';
  // Once flat, stop transforming text. A single aligned leaf bridges to the
  // already-laid-out live page, preventing per-band text rasterization jumps.
  if(motion===1){revealSpread();scene.style.visibility='hidden';if(stationary)stationary.style.visibility='hidden';landing.style.opacity='1';stage.style.opacity=String(Math.max(0,1-(t-.84)/.16));}
  stage.dataset.phase=motion===1?'settling':'turning';
  stage.dataset.progress=String(Math.round(progress*100));
  if(t<1)frame=requestAnimationFrame(draw);
  else{revealSpread();stage.remove();if(turnAnimation===handle){turnAnimation=null;turnStage=null}}
 }
 frame=requestAnimationFrame(draw);
}
function showBookPage(page){
 if(settings.documentStyle!=='notebook')return false;
 const step=bookStep(),count=$$('[data-page-number]').length;
 const before=bookPage===0?-1:Math.floor((bookPage-1)/step),after=page<=0?-1:Math.floor((Math.min(page,count)-1)/step);
 if(before===after){bookPage=page;return false}
 cancelPageTurn();if(scrollY>80)window.scrollTo({top:0,behavior:'instant'});
 const forward=after>before,animate=!matchMedia('(prefers-reduced-motion: reduce)').matches;
 const oldSpread=$$('.page-spread').find(p=>!p.hidden);
 const oldLeaves=$$('.scan-page',oldSpread).filter(p=>!p.hidden&&getComputedStyle(p).display!=='none');
 const turning=forward?oldLeaves.at(-1):oldLeaves[0],rect=turning.getBoundingClientRect();
 const front=animate?captureLeaf(turning):null;
 const stationary=animate&&step===2&&oldLeaves.length>1?captureLeaf(forward?oldLeaves[0]:oldLeaves.at(-1)):null;
 bookPage=Math.max(0,Math.min(page,count));syncBookView();sizeNotes();scheduleSettingsMask();
 if(front){
  const newSpread=$$('.page-spread').find(p=>!p.hidden);
  const newLeaves=$$('.scan-page',newSpread).filter(p=>!p.hidden&&getComputedStyle(p).display!=='none');
  const back=captureLeaf(forward?newLeaves[0]:newLeaves.at(-1));
  animateBookTurn(front,back,stationary,rect,forward,before===-1&&step===2?newSpread:null);
 }
 return true;
}
function turnBook(direction){const step=bookStep(),start=bookPage===0?0:Math.floor((bookPage-1)/step)*step+1;const target=start===0?(direction>0?1:-1):start===1&&direction<0?0:start+direction*step;if(target<0||target>$$('[data-page-number]').length)return;showBookPage(target)}
function smoothTo(el){if(el&&settings.documentStyle==='notebook'){const page=el.closest('[data-page-number]');if(page&&showBookPage(Number(page.dataset.pageNumber)))return}el?.scrollIntoView({block:'center',behavior:matchMedia('(prefers-reduced-motion: reduce)').matches?'instant':'smooth'})}

function locate(i,end=false){selectQuestion(i);smoothTo($('[data-question-'+(end?'end':'start')+'="'+i+'"]'))}
function refreshGrade(i){const r=record(i);$('[data-total="'+i+'"]').textContent=r.scores.reduce((a,b)=>a+b,0);$('[data-score-state="'+i+'"]').textContent=r.confirmed?'已核 ✓':'建议';const c=$('[data-confirm="'+i+'"]');c.textContent=r.confirmed?'撤回确认':'确认 ✓';$('[data-confirm-state="'+i+'"]').textContent=r.confirmed?'已复核':'';const count=[0,1].filter(j=>record(j).confirmed).length;$$('[data-progress]').forEach(el=>el.textContent=count+' / 2 已复核');$$('[data-completion]').forEach(el=>el.textContent=count===2?'本份作业已复核完毕':'本次提交结束')}
function commitScores(i){const inputs=$$('[data-score^="'+i+':"]');const qs=questions();const values=inputs.map(el=>Number(el.value));if(inputs.some((el,j)=>el.value===''||!Number.isFinite(values[j])||values[j]<0||values[j]>qs[i].criteria[j][1]||values[j]*2%1!==0)){announce('请输入范围内的分数，支持半分。',i);return false}record(i).scores=values;return true}
function confirmQuestion(i){selectQuestion(i);const r=record(i);if(r.confirmed){r.confirmed=false;refreshGrade(i);announce('已撤回确认，可继续修改。',i);return}if(!commitScores(i))return;r.confirmed=true;refreshGrade(i);const next=1-i;if(!record(next).confirmed){locate(next);announce('第 '+questions()[i].number+' 题已确认。',i)}else announce('本份作业已复核完毕。',i)}
function editScore(i){selectQuestion(i);const el=$('[data-rubric="'+i+'"]');el.hidden=!el.hidden;if(!el.hidden){smoothTo($('[data-grade-for="'+i+'"]'));requestAnimationFrame(()=>$('[data-score="'+i+':0"]').focus({preventScroll:true}))}}
function changeStudent(next){if(next<0||next>=students.length)return;cancelPageTurn();student=next;active=0;bookPage=0;render();window.scrollTo({top:0,behavior:'instant'})}
function bind(){
 $$('[data-question-region]').forEach(el=>{el.addEventListener('click',()=>selectQuestion(Number(el.dataset.questionRegion)));el.addEventListener('focusin',()=>selectQuestion(Number(el.dataset.questionRegion)))});
 $$('[data-edit-score]').forEach(b=>b.onclick=e=>{e.stopPropagation();editScore(Number(b.dataset.editScore))});
 $$('[data-close-rubric]').forEach(b=>b.onclick=()=>{$('[data-rubric="'+b.dataset.closeRubric+'"]').hidden=true});
 $$('[data-jump-end]').forEach(b=>b.onclick=()=>locate(Number(b.dataset.jumpEnd),true));
 $$('[data-turn]').forEach(b=>b.onclick=()=>{if(bookPage===0&&Number(b.dataset.turn)>0)requestLandscape();turnBook(Number(b.dataset.turn))});
 $$('[data-jump-page]').forEach(b=>b.onclick=()=>smoothTo($('[data-page-number="'+b.dataset.jumpPage+'"]')));
 $$('[data-score]').forEach(el=>el.onchange=()=>{const [i,j]=el.dataset.score.split(':').map(Number),v=Number(el.value),max=questions()[i].criteria[j][1];if(el.value===''||!Number.isFinite(v)||v<0||v>max||v*2%1!==0){el.value=record(i).scores[j];announce('分数应在 0—'+max+' 之间，支持半分。',i);return}record(i).scores[j]=v;record(i).confirmed=false;refreshGrade(i)});
 $$('[data-feedback]').forEach(el=>el.oninput=()=>{const i=Number(el.dataset.feedback);record(i).feedback=el.value;record(i).confirmed=false;refreshGrade(i);sizeNotes()});
 $$('[data-confirm]').forEach(b=>b.onclick=()=>confirmQuestion(Number(b.dataset.confirm)));
 $$('[data-next]').forEach(b=>b.onclick=()=>locate(1-Number(b.dataset.next)));
 $$('[data-next-student]').forEach(b=>{b.disabled=student===students.length-1;b.onclick=()=>changeStudent(student+1)});
 $$('[data-action]').forEach(b=>b.onclick=()=>action(b.dataset.action));
 $$('[data-preset]').forEach(b=>b.onclick=()=>{settings=sanitize({...settings,...presets[b.dataset.preset],preset:b.dataset.preset,subject:settings.subject,marks:settings.marks,reading:settings.reading});apply()});
 $$('[data-ink]').forEach(b=>b.onclick=()=>{settings.ink=b.dataset.ink;apply()});
 $$('input[name=document-style]').forEach(el=>el.onchange=()=>{if(el.value!=='notebook')return;settings.documentStyle='notebook';apply()});
 $$('input[name=reading]').forEach(el=>el.onchange=()=>{settings.reading=el.value;apply()});
 $('#panel-font').onchange=e=>{settings.panelFont=e.target.value;apply()};
 $$('input[name=background]').forEach(el=>el.onchange=()=>{settings.background=el.value;apply()});
 $('#subject').onchange=e=>{settings.subject=e.target.value;active=0;render()};
 $('#preference-note').oninput=e=>{note=e.target.value;updateChoice();persist()};
}
// Fade only manuscript ink. Paper, ruling and the book binding are untouched.
function syncSettingsMask(){
 const panel=$('#preferences');if(!panel)return;
 const layers=$$('.paper-tools,.document-heading,.page-running,.original-answer,.grade-ink,.teacher-writing,.page-next,.paper-footer,.submission-end,.cover-print',$('#manuscript'));
 const clear=el=>{el.style.maskImage='';el.style.webkitMaskImage='';el.style.maskComposite='';el.style.webkitMaskComposite='';delete el.dataset.settingsMasked};
 if(panel.hidden){layers.forEach(clear);return}
 const p=panel.getBoundingClientRect(),feather=42;
 for(const el of layers){
  const r=el.getBoundingClientRect();
  if(!r.width||!r.height||r.right<p.left-feather||r.left>p.right+feather||r.bottom<p.top-feather||r.top>p.bottom+feather){clear(el);continue}
  const sx=r.width/el.offsetWidth||1,sy=r.height/el.offsetHeight||1;
  const x=[p.left-feather,p.left,p.right,p.right+feather].map(v=>(v-r.left)/sx);
  const y=[p.top-feather,p.top,p.bottom,p.bottom+feather].map(v=>(v-r.top)/sy);
  const gradient=(direction,v)=>`linear-gradient(to ${direction},#000 ${v[0]}px,transparent ${v[1]}px,transparent ${v[2]}px,#000 ${v[3]}px)`;
  const mask=gradient('right',x)+','+gradient('bottom',y);
  el.style.webkitMaskImage=mask;el.style.webkitMaskComposite='source-over';el.style.maskImage=mask;el.style.maskComposite='add';el.dataset.settingsMasked='true';
 }
}
let settingsMaskFrame=0;
function scheduleSettingsMask(){if(settingsMaskFrame)return;settingsMaskFrame=requestAnimationFrame(()=>{settingsMaskFrame=0;syncSettingsMask()})}

function togglePreferences(force){prefsOpen=typeof force==='boolean'?force:!prefsOpen;$('#preferences').hidden=!prefsOpen;syncSettingsMask();$('[data-action="preferences"]').setAttribute('aria-expanded',prefsOpen);if(prefsOpen){renderCandidates();$('#preferences').scrollTop=0;}else if($('#preferences').contains(document.activeElement))$('[data-action=preferences]').focus({preventScroll:true})}
function action(name){if(name==='previous-student')changeStudent(student-1);else if(name==='next-student')changeStudent(student+1);else if(name==='preferences')togglePreferences();else if(name==='close-preferences')togglePreferences(false);else if(name==='toggle-zoom'){zoom=!zoom;apply()}else if(name==='toggle-marks'){settings.marks=!settings.marks;apply()}else if(name==='reset-style'){settings=sanitize({documentStyle:'notebook',preset:settings.preset,subject:settings.subject,reading:'double'});apply()}else if(name==='save-candidate'){if(candidates.length>=4)return;candidates.push({id:Date.now().toString(36),settings:{...settings}});persist();renderCandidates();announce(storageOK?'候选已保存在当前浏览器。':'候选仅暂存在当前页面，请下载备份。')}else if(name==='confirm-choice'){togglePreferences(true);$('#choice-section').hidden=false;confirmed={settings:{...settings},note,at:new Date().toISOString()};updateChoice();persist();smoothTo($('#choice-section'))}else if(name==='copy-choice')copyChoice();else if(name==='download-choice')downloadChoice()}
function renderCandidates(){$('#save-candidate').disabled=candidates.length>=4;$('#candidate-list').innerHTML=candidates.map((c,i)=>`<span class="candidate-item"><button data-candidate="${esc(c.id)}">候选 ${i+1} · ${presets[c.settings.preset].name}</button><button data-remove="${esc(c.id)}" aria-label="删除候选 ${i+1}">×</button></span>`).join('');$$('[data-candidate]').forEach(b=>b.onclick=()=>{const c=candidates.find(c=>c.id===b.dataset.candidate);const old=settings.subject;settings={...c.settings};if(old!==settings.subject)render();else apply();announce('已载入候选。')});$$('[data-remove]').forEach(b=>b.onclick=()=>{candidates=candidates.filter(c=>c.id!==b.dataset.remove);persist();renderCandidates()})}
function summary(){return `阅见：原稿上的无框批改\n样式：${documentStyles[settings.documentStyle]}；阅览：${readingModes[settings.reading]}；作业背景：${paperBackgrounds[settings.background]}；设置字体：${panelFonts[settings.panelFont]}\n方案：${presets[settings.preset].name}\n用墨：${pens[settings.ink]}；示例：${subjects[settings.subject]}\n我的意见：${note||'暂无'}\n设置：${JSON.stringify(settings)}`}
function updateChoice(){if(confirmed)confirmed={...confirmed,settings:{...settings},note};$('#preference-summary').value=summary()}
async function copyChoice(){updateChoice();try{await navigator.clipboard.writeText(summary());announce('已复制，请粘贴回对话。')}catch{$('#preference-summary').focus();$('#preference-summary').select();announce('请复制选中的偏好文字。')}}
function downloadChoice(){const url=URL.createObjectURL(new Blob([JSON.stringify({version:3,settings,note,candidates},null,2)],{type:'application/json'}));const a=document.createElement('a');a.href=url;a.download='阅见-原稿批改偏好.json';a.click();setTimeout(()=>URL.revokeObjectURL(url),2000)}
// The prototype's native sheet size. Real scan metadata will supply these
// dimensions directly; viewport width never changes paper coordinates.
const sheet={width:720,height:1020};
function fitPaper(){
 const root=$('#manuscript'),viewport=$('#paper-viewport');
 const width=sheet.width*bookStep(),height=sheet.height;
 const availableWidth=Math.max(1,document.documentElement.clientWidth-48);
 const availableHeight=Math.max(1,window.innerHeight-64);
 const scale=Math.min(availableWidth/width,availableHeight/height)*(zoom?1.65:1);
 root.style.setProperty('--sheet-width',sheet.width+'px');root.style.setProperty('--sheet-height',height+'px');
 root.style.setProperty('--canvas-width',width+'px');root.style.setProperty('--view-scale',scale);
 viewport.style.width=(width*scale+32)+'px';viewport.style.height=(height*scale+32)+'px';
 root.dataset.displayScale=scale.toFixed(4);
 // Anchor the UI to the stationary paper surface, not the browser viewport.
 // Keep it legible at normal sizes and fit it inside even a small cover leaf.
 const inset=20*scale,uiScale=Math.min(1,(sheet.width*scale-2*inset)/370);
 viewport.style.setProperty('--paper-inset',(16+inset)+'px');
 viewport.style.setProperty('--paper-ui-scale',uiScale);
 viewport.style.setProperty('--paper-settings-top',(16+inset+54*uiScale)+'px');
 viewport.style.setProperty('--paper-settings-height',Math.max(0,(height*scale-2*inset-54*uiScale)/uiScale)+'px');
}
let orientationAttempted=false;
async function requestLandscape(force=false){
 if(innerWidth>900||innerWidth>=innerHeight||(!force&&!matchMedia('(pointer:coarse)').matches)||orientationAttempted&&!force)return;
 orientationAttempted=true;
 const hint=$('#landscape');
 if(typeof screen.orientation?.lock!=='function'){hint.textContent='请将手机横置阅读';return}
 try{
  if(!document.fullscreenElement&&document.documentElement.requestFullscreen)await document.documentElement.requestFullscreen();
  await screen.orientation.lock('landscape');
 }catch{hint.textContent='请将手机横置阅读'}
}
$('#landscape').onclick=()=>requestLandscape(true);
window.addEventListener('resize',()=>{cancelPageTurn();fitPaper();syncSettingsMask()});
window.addEventListener('scroll',scheduleSettingsMask,{passive:true});
document.addEventListener('keydown',e=>{if(settings.documentStyle==='notebook'&&!prefsOpen&&!e.target.closest('input,textarea,select,[contenteditable]')&&!e.metaKey&&!e.ctrlKey&&!e.altKey&&['ArrowLeft','ArrowRight'].includes(e.key)){e.preventDefault();turnBook(e.key==='ArrowRight'?1:-1)}if((e.metaKey||e.ctrlKey)&&e.key==='Enter'&&settings.marks){e.preventDefault();confirmQuestion(active)}if(e.key==='Escape'){togglePreferences(false);$$('[data-rubric]').forEach(el=>el.hidden=true)}});
render();
// Expose only the same preference actions as the visible on-paper controls.
const context=document.modelContext;
if(context?.registerTool){const lifecycle=new AbortController();const tools=[{name:'read_design_preferences',title:'读取纸上批改偏好',description:'读取当前外观、候选与本地确认结果，不修改状态。',inputSchema:{type:'object',properties:{},additionalProperties:false},annotations:{readOnlyHint:true,untrustedContentHint:true},execute(input){if(!input||typeof input!=='object'||Object.keys(input).length)throw new Error('此工具不接受参数');return {settings,candidates,confirmed,note,activeQuestion:active}}},{name:'configure_design_preview',title:'调整原稿外观',description:'调整纸上可见设置并保存在当前浏览器，不会提交偏好或成绩。',inputSchema:{type:'object',properties:{documentStyle:{type:'string',enum:['notebook']},panelFont:{type:'string',enum:Object.keys(panelFonts)},background:{type:'string',enum:Object.keys(paperBackgrounds)},reading:{type:'string',enum:Object.keys(readingModes)},preset:{type:'string',enum:Object.keys(presets)},ink:{type:'string',enum:Object.keys(pens)},marks:{type:'boolean'},subject:{type:'string',enum:Object.keys(subjects)}},additionalProperties:false},annotations:{readOnlyHint:false,untrustedContentHint:false},execute(input){if(!input||typeof input!=='object'||Array.isArray(input)||Object.keys(input).some(k=>!Object.hasOwn(settings,k)))throw new Error('参数无效');let base=input.preset&&presets[input.preset]?{...settings,...presets[input.preset]}:settings;if(input.documentStyle&&input.documentStyle!==settings.documentStyle)base={...base,reading:input.documentStyle==='notebook'?'double':'single',background:input.documentStyle==='notebook'?'ruled':'plain'};const candidate=sanitize({...base,...input});if(Object.entries(input).some(([k,v])=>candidate[k]!==v))throw new Error('设置超出允许范围');const old=settings.subject;settings=candidate;if(old!==settings.subject)render();else apply();return {settings}}}];for(const tool of tools){try{Promise.resolve(context.registerTool(tool,{signal:lifecycle.signal})).catch(()=>{})}catch{}}window.addEventListener('pagehide',()=>lifecycle.abort(),{once:true})}
