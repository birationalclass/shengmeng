import {renderNotebook,renderCoverPrint} from './notebook.js?v=20260927-edge-turn';
import {getDemoQuestion,getDemoGrade} from './demo-grader.js';
const $=(s,root=document)=>root.querySelector(s), $$=(s,root=document)=>[...root.querySelectorAll(s)];
const esc=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
// Synthetic identities for browsing eight notebooks; no real student data.
const students=Array.from({length:8},(_,i)=>({name:'测试同学 '+String(i+1).padStart(2,'0'),id:'DEMO-'+String(i+1).padStart(3,'0')}));
const subjects={university:'大学数学',secondary:'中学数学',general:'通用作业'};
const panelFonts={sans:'简洁体',song:'宋体',hand:'手写体'};
const paperBackgrounds={plain:'空白',ruled:'横线本',grid:'方格本',tian:'田字格'};
const documentStyles={exam:'试卷',notebook:'作业本'};
const readingModes={single:'单页',double:'双页'};
const icon=body=>`<svg viewBox="0 0 24 24" aria-hidden="true" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round">${body}</svg>`;
const icons={home:icon('<path d="m3 10 9-7 9 7M5 9v12h5v-7h4v7h5V9"/>'),settings:icon('<path d="m9 3-.7 2.3-2.2 1L4 5.7l-2 3.5 1.7 1.6v2.5L2 14.8l2 3.5 2.1-.6 2.2 1L9 21h4l.7-2.3 2.2-1 2.1.6 2-3.5-1.7-1.5v-2.5L20 9.2l-2-3.5-2.1.6-2.2-1L13 3Z"/><circle cx="11" cy="12" r="3"/>'),zoom:icon('<path d="M8 3H3v5m13-5h5v5M3 16v5h5m13-5v5h-5"/>'),marks:icon('<path d="M2 12s4-7 10-7 10 7 10 7-4 7-10 7-10-7-10-7Z"/><circle cx="12" cy="12" r="3"/><path class="eye-off" d="m3 3 18 18"/>'),single:icon('<path d="M6 3h12v18H6zM9 8h6m-6 4h6m-6 4h4"/>'),double:icon('<path d="M2 4h9v16H2zM13 4h9v16h-9zM5 9h3m-3 4h3m8-4h3m-3 4h3"/>')};
const pens={'#af4b45':'朱批','#476d8f':'蓝墨','#595b60':'石墨'};
const presets={studio:{name:'清朗',ink:'#af4b45'},pro:{name:'石墨',ink:'#595b60'},paper:{name:'纸感',ink:'#af4b45'}};
const key='yuejian-paper-preferences-v3';
let storageOK=true;
function read(){try{return JSON.parse(localStorage.getItem(key))||{}}catch{storageOK=false;return {}}}
const stored=read();
function sanitize(v={}){const p=Object.hasOwn(presets,v.preset)?v.preset:'studio',base=presets[p],documentStyle='notebook';return {documentStyle,animations:typeof v.animations==='boolean'?v.animations:true,motionSpeed:v.motionSpeed==='fast'?'fast':'slow',panelFont:Object.hasOwn(panelFonts,v.panelFont)?v.panelFont:'sans',background:Object.hasOwn(paperBackgrounds,v.background)?v.background:(documentStyle==='notebook'?'ruled':'plain'),reading:v.documentStyle!=='exam'&&Object.hasOwn(readingModes,v.reading)?v.reading:'double',preset:p,ink:Object.hasOwn(pens,v.ink)?v.ink:base.ink,marks:typeof v.marks==='boolean'?v.marks:true,subject:Object.hasOwn(subjects,v.subject)?v.subject:'university'}}
let settings=sanitize(stored.notebookDefaults?stored.settings:{...stored.settings,documentStyle:'notebook',reading:'double'}),candidates=Array.isArray(stored.candidates)?stored.candidates.slice(0,4).map(c=>({id:String(c.id),settings:sanitize(c.settings)})):[];
let note=typeof stored.note==='string'?stored.note:'',confirmed=stored.confirmed||null;
// Start with neighbours on both sides so both directions can be explored.
let student=1,active=0,prefsOpen=false;
let settingsObserver;
let bookPage=0,turnAnimation=null,turnStage=null;
const motionEnabled=()=>settings.animations&&!matchMedia('(prefers-reduced-motion: reduce)').matches;
const motionRate=()=>settings.motionSpeed==='fast'?2:1;
let notebookInteractionLocked=false;
function runNotebookMotion(action){
 if(notebookInteractionLocked)return false;
 notebookInteractionLocked=true;
 document.body.classList.add('notebook-interaction-locked');
 $('#paper-viewport').setAttribute('aria-busy','true');
 const unlock=()=>{
  notebookInteractionLocked=false;
  document.body.classList.remove('notebook-interaction-locked');
  $('#paper-viewport').removeAttribute('aria-busy');
 };
 if(!motionEnabled()){try{action()}finally{unlock()}return true}
 const waitForFinish=()=>{if(turnStage)requestAnimationFrame(waitForFinish);else unlock()};
 // Complete the highlight fade before creating any moving surface. One lock
 // spans closing, parking, flipping and straightening, including callbacks.
 setTimeout(()=>{
  try{action();requestAnimationFrame(waitForFinish)}catch(error){unlock();throw error}
 },600/motionRate());
 return true;
}
for(const type of ['click','pointerdown','keydown'])document.addEventListener(type,event=>{
 if(notebookInteractionLocked&&(event.target.closest?.('#paper-viewport,.page-turn-stage')||(type==='keydown'&&['ArrowLeft','ArrowRight'].includes(event.key)))){
  event.preventDefault();event.stopImmediatePropagation();
 }
},true);

const nextBookPose={angle:5,x:28,y:28};
const records={};
const record=i=>{const id=[settings.subject,student,i].join('-');return records[id]||(records[id]=getDemoGrade(settings.subject,student,i))};
const questions=()=>[getDemoQuestion(settings.subject,student,0),getDemoQuestion(settings.subject,student,1)];
function persist(){try{localStorage.setItem(key,JSON.stringify({settings,candidates,note,confirmed,notebookDefaults:1}));storageOK=true}catch{storageOK=false}return storageOK}
function announce(text,i=active){const s=$('#status');if(s)s.textContent=text;const near=$('[data-confirm-state="'+i+'"]');if(near)near.textContent=text}
function prefMarkup(){return `<section class="paper-preferences" id="preferences" ${prefsOpen?'':'hidden'} aria-label="设置"><div class="preference-heading"><strong>设置</strong><button data-action="close-preferences" aria-label="关闭设置">收起 ↑</button></div><fieldset class="document-style-settings"><legend>文稿样式</legend><div class="document-style-options">${Object.entries(documentStyles).map(([id,name])=>`<label class="document-style-option"><input type="radio" name="document-style" value="${id}" ${id==='exam'?'disabled aria-label="试卷（暂未开放）"':''} ${settings.documentStyle===id?'checked':''}><span class="style-preview style-preview-${id}" aria-hidden="true"><i></i><i></i></span><span>${name}${id==='exam'?'<small>暂未开放</small>':''}</span></label>`).join('')}</div></fieldset><fieldset class="reading-settings"><legend>阅览方式</legend><div class="reading-options">${Object.entries(readingModes).map(([id,name])=>`<label class="reading-option"><input type="radio" name="reading" value="${id}" ${settings.reading===id?'checked':''}><span>${icons[id]}${name}</span></label>`).join('')}</div><p class="reading-hint">${settings.reading==='double'?'双页并排，按原稿顺序连续阅读。':'单页居中，向下连续阅读。'}</p><p class="narrow-reading-hint" ${settings.reading==='double'?'':'hidden'}>纸张比例固定，窗口只改变整体显示倍率。</p></fieldset><fieldset class="animation-settings"><legend>动画</legend><label class="animation-toggle"><input id="animations-enabled" type="checkbox" ${settings.animations?'checked':''}>启用动画</label><span class="animation-direct">关闭后直接显示</span><div class="animation-speeds" role="group" aria-label="动画速度">${[['slow','慢 · 原速'],['fast','快 · 两倍速']].map(([value,label])=>`<label><input type="radio" name="motion-speed" value="${value}" ${settings.motionSpeed===value?'checked':''} ${settings.animations?'':'disabled'}><span>${label}</span></label>`).join('')}</div></fieldset><fieldset class="paper-background-settings"><legend>作业背景</legend><div class="background-options">${Object.entries(paperBackgrounds).map(([id,name])=>`<label class="background-option"><input type="radio" name="background" value="${id}" ${settings.background===id?'checked':''}><span class="paper-sample" data-paper="${id}" aria-hidden="true"></span><span>${name}</span></label>`).join('')}</div></fieldset><label class="pref-field panel-font-field">设置字体<select id="panel-font">${Object.entries(panelFonts).map(([id,name])=>`<option value="${id}" ${settings.panelFont===id?'selected':''}>${name}</option>`).join('')}</select></label><div class="preset-options" role="group" aria-label="外观方案">${Object.entries(presets).map(([id,p])=>`<button data-preset="${id}" aria-pressed="${id===settings.preset}">${p.name}</button>`).join('')}</div><div class="preference-controls"><div class="pref-field"><span>批注用墨</span><div class="pen-colors" role="group" aria-label="批注颜色">${Object.entries(pens).map(([color,name])=>`<button style="color:${color}" data-ink="${color}" aria-label="${name}" aria-pressed="${settings.ink===color}" title="${name}">✓</button>`).join('')}</div></div><label class="pref-field">示例学科<select id="subject">${Object.entries(subjects).map(([id,name])=>`<option value="${id}" ${id===settings.subject?'selected':''}>${name}</option>`).join('')}</select></label><button data-action="toggle-marks" id="marks-setting">${settings.marks?'隐藏批注':'显示批注'}</button></div><div class="preference-actions"><button data-action="confirm-choice">选定此版</button><button data-action="save-candidate" id="save-candidate">保留一个候选</button><button data-action="reset-style">恢复默认</button></div><div id="candidate-list" class="candidate-list"></div><p class="preference-help">仅保存在当前浏览器。选定后可复制偏好给我。</p><section id="choice-section" class="choice-section" hidden><label for="preference-note">还想怎样调整？</label><textarea id="preference-note" placeholder="例如：批注更贴近答案，或分数再小一些。">${esc(note)}</textarea><div class="preference-actions"><button data-action="copy-choice">复制偏好</button><button data-action="download-choice">下载偏好</button></div><textarea readonly id="preference-summary" class="preference-summary" aria-label="可复制的设计偏好"></textarea><p class="preference-help">复制后粘贴到对话中；这里不会自动发送。</p></section></section>`}
function render(){const s=students[student];const qs=questions();
 const account=$('.auth-entry');if(account)$('#homework-auth').append(account);
 const tools=`<div class="paper-tools"><div class="paper-identity"><a class="wordmark" href="../" aria-label="返回课程主页">阅见</a><span>原稿演示</span><span class="paper-progress" data-progress></span></div></div>`;
 $('#workspace-tools').innerHTML=`<div class="paper-controls"><a class="home-link icon-button" href="../" aria-label="课程主页" data-tip="主页">${icons.home}</a><span id="account-slot"></span><button class="icon-button" data-action="preferences" aria-label="设置" aria-controls="preferences" aria-expanded="${prefsOpen}" data-tip="设置">${icons.settings}</button></div>`;
 if(account&&!document.body.classList.contains('has-homework-session'))$('#account-slot').append(account);
 window.dispatchEvent(new Event('homework-tools-ready'));
 $('#reading-footer').innerHTML=`<div class="paper-controls"><label class="student-label">${s.name} · <input id="book-jump" type="number" min="1" max="${students.length}" value="${student+1}" aria-label="跳到第几本作业" title="输入本数并回车，可测试第 ${students.length-1}→${students.length} 本"> / ${students.length}</label><button class="icon-button" data-action="toggle-marks" id="marks" aria-label="隐藏批注" aria-pressed="${settings.marks}" data-tip="隐藏批注">${icons.marks}</button><button class="icon-button" data-action="toggle-zoom" id="zoom" aria-label="全屏" aria-pressed="${Boolean(document.fullscreenElement)}" data-tip="全屏">${icons.zoom}</button></div><span id="reader-status" role="status"></span>`;
 const previousLayers=Array.from({length:Math.min(2,Math.max(0,student-1))},(_,i)=>i+1).reverse().map(depth=>`<div class="adjacent-book previous-book-layer" style="--stack-depth:${depth}" aria-hidden="true"><span class="back-cover-binding"></span></div>`).join('');
 const nextLayers=Array.from({length:Math.min(2,Math.max(0,students.length-student-2))},(_,i)=>i+1).reverse().map(depth=>`<div class="adjacent-book next-book-layer" style="--stack-depth:${depth}" aria-hidden="true"><span class="stack-cover-preview">${renderCoverPrint(students[student+1+depth],getDemoQuestion(settings.subject,student+1+depth,0).paper)}</span></div>`).join('');
 $('#notebook-stack').innerHTML=`${nextLayers}${previousLayers}${student>0?`<button class="adjacent-book previous-book" data-action="previous-student" aria-label="上一本：${students[student-1].name}，封底"><span class="back-cover-binding" aria-hidden="true"></span></button>`:''}${student<students.length-1?`<button class="adjacent-book next-book" data-action="next-student" aria-label="下一本：${students[student+1].name}"><span class="stack-cover-preview" aria-hidden="true">${renderCoverPrint(students[student+1],getDemoQuestion(settings.subject,student+1,0).paper)}</span></button>`:''}`;
 $('#settings-root').innerHTML=prefMarkup();
 settingsObserver?.disconnect();settingsObserver=new ResizeObserver(syncSettingsMask);settingsObserver.observe($('#preferences'));
 $('#paper-viewport').dataset.lastBook=String(student===students.length-1);
 $('#manuscript').innerHTML=renderNotebook({questions:qs,student:{...s,correct:student===1&&settings.subject!=='general'},grades:[record(0),record(1)],tools});
 bind();apply();refreshGrade(0);refreshGrade(1);selectQuestion(active);renderCandidates();sizeNotes();
}
function apply(){cancelPageTurn();$('#animations-enabled').checked=settings.animations;$$('input[name=motion-speed]').forEach(el=>{el.checked=el.value===settings.motionSpeed;el.disabled=!settings.animations});document.documentElement.style.setProperty('--highlight-duration',(settings.animations?450/motionRate():0)+'ms');document.documentElement.style.setProperty('--corner-return-duration',(settings.animations?600/motionRate():0)+'ms');const root=$('#manuscript');document.documentElement.style.setProperty('--ink',settings.ink);document.documentElement.dataset.panelFont=settings.panelFont;root.dataset.paper=settings.background;root.dataset.documentStyle=settings.documentStyle;$$('input[name=document-style]').forEach(el=>el.checked=el.value===settings.documentStyle);$$('[data-document-kind]').forEach(el=>el.textContent=documentStyles[settings.documentStyle]);$('#panel-font').value=settings.panelFont;$$('input[name=background]').forEach(el=>el.checked=el.value===settings.background);root.style.setProperty('--ink',settings.ink);root.style.setProperty('--paper',settings.documentStyle==='notebook'?'#fffef9':(settings.preset==='paper'?'#fffef8':'#fff')); root.classList.toggle('no-marks',!settings.marks);root.dataset.reading=settings.reading;$$('input[name=reading]').forEach(el=>el.checked=el.value===settings.reading);$('.reading-hint').textContent=settings.reading==='double'?(settings.documentStyle==='notebook'?'左右对页，点击纸页外侧边缘翻页。':'两张试卷并排，按原稿顺序连续阅读。'):(settings.documentStyle==='notebook'?'每次一页，点击纸页外侧边缘翻页。':'单页居中，向下连续阅读。');$('.narrow-reading-hint').hidden=true;$$('[data-preset]').forEach(b=>b.setAttribute('aria-pressed',b.dataset.preset===settings.preset));$$('[data-ink]').forEach(b=>b.setAttribute('aria-pressed',b.dataset.ink===settings.ink));for(const [id,label,pressed] of [['marks',settings.marks?'隐藏批注':'显示批注',settings.marks],['zoom',document.fullscreenElement?'退出全屏':'全屏',Boolean(document.fullscreenElement)]]){const b=$('#'+id);b.setAttribute('aria-label',label);b.setAttribute('aria-pressed',pressed);b.dataset.tip=label;}if($('#marks-setting'))$('#marks-setting').textContent=settings.marks?'隐藏批注':'显示批注';syncBookView();fitPaper();sizeNotes();scheduleSettingsMask();persist()}
function selectQuestion(i){active=i;$$('[data-question-region]').forEach(r=>r.dataset.active=String(Number(r.dataset.questionRegion)===i))}
function sizeNotes(){$$('.ink-comment').forEach(t=>{t.style.height='auto';t.style.height=Math.max(36,t.scrollHeight)+'px'})}
const bookStep=()=>settings.reading==='double'?2:1;
function syncBookView(){
 const notebook=settings.documentStyle==='notebook',step=bookStep();
 const pages=$$('[data-page-number]');bookPage=Math.max(0,Math.min(bookPage,pages.length));
 const cover=notebook&&bookPage===0;
 $('#paper-viewport').dataset.bookOpen=String(!cover);
 const start=step===2?Math.floor((Math.max(1,bookPage)-1)/2)*2+1:Math.max(1,bookPage);
 $$('.page-spread').forEach(spread=>spread.hidden=spread.classList.contains('cover-spread')?!cover:cover||(notebook&&!$$('[data-page-number]',spread).some(p=>Number(p.dataset.pageNumber)>=start&&Number(p.dataset.pageNumber)<start+step)));
 pages.forEach(page=>page.hidden=cover||(notebook&&(Number(page.dataset.pageNumber)<start||Number(page.dataset.pageNumber)>=start+step)));
 $$('[data-turn]').forEach(b=>{b.disabled=Number(b.dataset.turn)<0?cover:!cover&&start+step>pages.length;if(b.classList.contains('book-previous'))b.setAttribute('aria-label',start===1?'合上封面':'上一页')});
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
function animateBookTurn(front,back,stationary,rect,forward,openingSpread=null,onComplete=null){
 const stage=document.createElement('div');stage.className='page-turn-stage';stage.inert=true;stage.setAttribute('aria-hidden','true');
 if(stationary)stage.append(stationary);
 const shadow=document.createElement('div');shadow.className='turn-contact-shadow';
 Object.assign(shadow.style,{left:rect.left+'px',top:rect.top+'px',width:rect.width+'px',height:rect.height+'px',background:`linear-gradient(${forward?'90deg':'270deg'},rgba(40,37,25,.24),transparent 75%)`});stage.append(shadow);
 const scene=document.createElement('div');scene.className='page-turn-scene';
 const pivot=forward?rect.left:rect.right,direction=forward?1:-1,w=rect.width,h=rect.height,count=16,bandWidth=w/count;
 scene.style.perspectiveOrigin=pivot+'px '+(rect.top+h/2)+'px';stage.append(scene);
 const coverTurn=front.firstElementChild.matches('.notebook-cover,.notebook-inner-cover');
 const ease=v=>{v=Math.max(0,Math.min(1,v));return v*v*(3-2*v)};
 const bands=[],shades=[];
 for(let i=0;i<count;i++){
  const band=document.createElement('div');band.className='turn-band';band.style.width=bandWidth+'px';band.style.height=h+'px';
  for(const [source,isBack] of [[front,false],[back,true]]){
   const face=document.createElement('div');face.className='turn-face'+(isBack?' turn-face-back':'');face.style.width=(bandWidth+.6)+'px';
   // A turning cover is green card alone; the page-block edge stays below.
   const coverFace=source.firstElementChild.matches('.notebook-cover,.notebook-inner-cover');
   face.style.bottom=-Math.max(3,3*w/sheet.width)+'px';face.style.transformOrigin=(bandWidth/2)+'px 50%';
   const copy=source.cloneNode(true),offset=(forward!==isBack)?i*bandWidth:w-(i+1)*bandWidth;
   if(coverFace){copy.classList.add('turn-cover-only');if(copy.firstElementChild.classList.contains('notebook-inner-cover'))copy.firstElementChild.style.height=`calc(${sheet.height}px + 3px * var(--binding-open,0))`;copy.firstElementChild.style.boxShadow=source.firstElementChild.classList.contains('notebook-cover')?'inset 7px 0 12px -10px #1c372f80':'inset -7px 0 12px -10px #1c372f80';}
   Object.assign(copy.style,{left:-offset+'px',top:'0',width:w+'px',height:h+'px',boxShadow:'none'});face.append(copy);
   const shade=document.createElement('div');shade.className='turn-shading';shades.push({element:shade,band:i,back:isBack});face.append(shade);band.append(face);
  }
  scene.append(band);bands.push(band);
 }
 const landing=back.cloneNode(true);landing.classList.add('turn-landing');landing.style.opacity='0';stage.append(landing);
 // Keep the destination's empty left half empty until the cover has landed.
 // Clip the whole spread, including its paper, binding and outer shadows.
 openingSpread?.classList.add('cover-opening');
 const revealSpread=()=>openingSpread?.classList.remove('cover-opening');
 document.body.append(stage);turnStage=stage;
 let frame=0,startTime,lastBinding;
 const handle={cancel(){cancelAnimationFrame(frame);revealSpread()}};turnAnimation=handle;
 function draw(now){
  if(startTime===undefined)startTime=now;
  const t=Math.min(1,((now-startTime)*motionRate())/(coverTurn?1300:1020)),motion=Math.min(1,t/.84);
  // Keep angular velocity continuous through the midpoint. Unfold across
  // that interval instead of dwelling edge-on with both faces invisible.
  const progress=(1-Math.cos(Math.PI*motion))/2;
  const unfolding=ease((motion-.36)/.28);
  const binding=forward?unfolding:1-unfolding;
  if(coverTurn&&binding!==lastBinding){stage.style.setProperty('--binding-open',String(binding));lastBinding=binding}
  const wave=motion===1?0:Math.sin(Math.PI*progress);
  const base=Math.PI*progress,bend=(coverTurn?.3:.9)*wave;
  let x=0,z=0;
  for(let i=0;i<count;i++){
   const u=(i+.5)/count,angle=base+bend*(u-.5);
   const dx=motion===1?-bandWidth:bandWidth*Math.cos(angle),dz=motion===1?0:bandWidth*Math.sin(angle);
   // Adjacent bands share the same vertical endpoints; individual lifts
   // produce a stepped bottom edge and cracks between otherwise joined bands.
   bands[i].style.transform=`translate3d(${pivot+direction*(x+dx/2)-bandWidth/2}px,${rect.top}px,${z+dz/2}px) rotateY(${-direction*angle}rad)`;

   x+=dx;z+=dz;
  }
  for(const shade of shades)shade.element.style.opacity=String(wave*(.05+.12*(shade.band+.5)/count)*(shade.back?.7:1));
  shadow.style.opacity=String(wave*.65);
  shadow.style.transform=`scaleX(${.45+.55*Math.abs(Math.cos(base))})`;
  shadow.style.transformOrigin=forward?'left':'right';
  // Once flat, stop transforming text. A single aligned leaf bridges to the
  // already-laid-out live page, preventing per-band text rasterization jumps.
  if(motion===1){revealSpread();scene.remove();stationary?.remove();landing.style.opacity='1';stage.style.opacity=String(Math.max(0,1-(t-.84)/.16));}
  stage.dataset.phase=motion===1?'settling':coverTurn&&motion>=.36&&motion<=.64?'unfolding-binding':'turning';
  stage.dataset.progress=String(Math.round(progress*100));
  if(t<1)frame=requestAnimationFrame(draw);
  else{revealSpread();stage.remove();if(turnAnimation===handle){turnAnimation=null;turnStage=null}onComplete?.()}
 }
 frame=requestAnimationFrame(draw);
}
function showBookPage(page,onComplete=null){
 if(settings.documentStyle!=='notebook')return false;
 const step=bookStep(),count=$$('[data-page-number]').length;
 const before=bookPage===0?-1:Math.floor((bookPage-1)/step),after=page<=0?-1:Math.floor((Math.min(page,count)-1)/step);
 if(before===after){bookPage=page;return false}
 if(!notebookInteractionLocked)return runNotebookMotion(()=>showBookPage(page,onComplete));
 cancelPageTurn();if(scrollY>80)window.scrollTo({top:0,behavior:'instant'});
 const forward=after>before,animate=motionEnabled();
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
  animateBookTurn(front,back,stationary,rect,forward,before===-1&&step===2?newSpread:null,onComplete);
 }else onComplete?.();
 return true;
}
function turnBook(direction){const step=bookStep(),start=bookPage===0?0:Math.floor((bookPage-1)/step)*step+1;const target=start===0?(direction>0?1:-1):start===1&&direction<0?0:start+direction*step;if(target<0||target>$$('[data-page-number]').length)return;showBookPage(target)}
function smoothTo(el){if(el&&settings.documentStyle==='notebook'){const page=el.closest('[data-page-number]');if(page&&showBookPage(Number(page.dataset.pageNumber)))return}el?.scrollIntoView({block:'center',behavior:motionEnabled()?'smooth':'instant'})}

function locate(i,end=false){selectQuestion(i);smoothTo($('[data-question-'+(end?'end':'start')+'="'+i+'"]'))}
function refreshGrade(i){const r=record(i);$('[data-total="'+i+'"]').textContent=r.scores.reduce((a,b)=>a+b,0);$('[data-score-state="'+i+'"]').textContent=r.confirmed?'已核 ✓':'建议';const c=$('[data-confirm="'+i+'"]');c.textContent=r.confirmed?'撤回确认':'确认 ✓';$('[data-confirm-state="'+i+'"]').textContent=r.confirmed?'已复核':'';const count=[0,1].filter(j=>record(j).confirmed).length;$$('[data-progress]').forEach(el=>el.textContent=count+' / 2 已复核');$$('[data-completion]').forEach(el=>el.textContent=count===2?'本份作业已复核完毕':'本次提交结束')}
function commitScores(i){const inputs=$$('[data-score^="'+i+':"]');const qs=questions();const values=inputs.map(el=>Number(el.value));if(inputs.some((el,j)=>el.value===''||!Number.isFinite(values[j])||values[j]<0||values[j]>qs[i].criteria[j][1]||values[j]*2%1!==0)){announce('请输入范围内的分数，支持半分。',i);return false}record(i).scores=values;return true}
function confirmQuestion(i){selectQuestion(i);const r=record(i);if(r.confirmed){r.confirmed=false;refreshGrade(i);announce('已撤回确认，可继续修改。',i);return}if(!commitScores(i))return;r.confirmed=true;refreshGrade(i);const next=1-i;if(!record(next).confirmed){locate(next);announce('第 '+questions()[i].number+' 题已确认。',i)}else announce('本份作业已复核完毕。',i)}
function editScore(i){selectQuestion(i);const el=$('[data-rubric="'+i+'"]');el.hidden=!el.hidden;if(!el.hidden){smoothTo($('[data-grade-for="'+i+'"]'));requestAnimationFrame(()=>$('[data-score="'+i+':0"]').focus({preventScroll:true}))}}
// Only this disposable copy moves. The neighbouring book and the current
// manuscript remain untouched until the copy has landed on the active book.
function closeNotebookToLeft(next){
 cancelPageTurn();togglePreferences(false);
 const root=$('#manuscript'),rect=root.getBoundingClientRect(),scale=rect.width/root.offsetWidth,w=sheet.width*scale,h=sheet.height*scale;
 const spread=$$('.page-spread').find(p=>!p.hidden),leaves=$$('.scan-page',spread).filter(p=>!p.hidden&&getComputedStyle(p).display!=='none');
 const front=captureLeaf(leaves.at(-1)),stationary=leaves.length>1?captureLeaf(leaves[0]):null;
 const template=document.createElement('div');template.className='adjacent-book previous-book';template.innerHTML='<span class="back-cover-binding" aria-hidden="true"></span>';
 Object.assign(template.style,{left:'0',top:'0',transform:'none'});root.append(template);const back=captureLeaf(template);template.remove();
 const stage=document.createElement('div');stage.className='page-turn-stage book-transfer-stage';stage.dataset.direction='left';stage.dataset.closeDirection='left';stage.dataset.phase='closing';stage.inert=true;stage.setAttribute('aria-hidden','true');
 const pivot=rect.right-w,top=rect.top;stage.style.perspectiveOrigin=`${pivot}px ${top+h/2}px`;
 if(stationary)stage.append(stationary);
 const flight=document.createElement('div');flight.className='book-transfer-copy';Object.assign(flight.style,{width:w+'px',height:h+'px',transformOrigin:'0 50%'});
 for(const [copy,reverse] of [[front,false],[back,true]]){
  Object.assign(copy.style,{left:'0',top:'0',width:w+'px',height:h+'px'});copy.firstElementChild.style.transform=`scale(${scale})`;
  const face=document.createElement('div');face.className='book-transfer-face'+(reverse?' book-transfer-back':'');face.append(copy);flight.append(face);
 }
 stage.append(flight);document.body.append(stage);turnStage=stage;
 const viewport=$('#paper-viewport');viewport.classList.add('book-leaving');const restore=()=>viewport.classList.remove('book-leaving');
 const neighbour=$('#notebook-stack .previous-book')?.getBoundingClientRect();
 const destination=neighbour?{x:neighbour.left+neighbour.width/2,y:neighbour.top+neighbour.height/2}:{x:rect.left+(-125+sheet.width/2)*scale,y:top+(9+sheet.height/2)*scale};
 let frame=0,startTime,landed=null,placedAt;
 const handle={cancel(){cancelAnimationFrame(frame);restore();stage.remove();}};turnAnimation=handle;
 function draw(now){
  if(startTime===undefined)startTime=now;
  const elapsed=(now-startTime)*motionRate(),t=Math.min(1,elapsed/850),p=(1-Math.cos(Math.PI*t))/2;
  flight.style.transform=`translate3d(${pivot}px,${top}px,0) rotateY(${-180*p}deg)`;
  stage.dataset.progress=String(Math.round(p*100));
  if(t===1){
   // Closing to the left exposes the back cover. Carry that same closed
   // book onto the left pile; never snap it back to the right-hand cover.
   // Captured descendants have explicit visibility, so hiding their parent
   // cannot retire them. Remove the old folding faces in this same frame.
   if(!landed){landed=document.createElement('div');landed.className='book-settle-copy';Object.assign(landed.style,{width:w+'px',height:h+'px',transformOrigin:'50% 50%'});landed.append(back.cloneNode(true));stage.append(landed);flight.remove();stationary?.remove();}
   const u=Math.min(1,(elapsed-850)/380),q=u*u*(3-2*u),startX=pivot-w/2,startY=top+h/2;
   landed.style.transform=`translate(${startX+(destination.x-startX)*q-w/2}px,${startY+(destination.y-startY)*q-h/2}px) rotate(${-2*q}deg)`;
   stage.dataset.phase='placing';
   if(u===1){
    stage.dataset.phase='placed';placedAt??=now;
    if(now-placedAt>=120/motionRate()){settleNextNotebook(next,stage,restore);return;}
   }
  }
  frame=requestAnimationFrame(draw);
 }
 flight.style.transform=`translate3d(${pivot}px,${top}px,0)`;frame=requestAnimationFrame(draw);
}
function flipNotebook(direction){
 const next=student+direction,incoming=direction<0;
 if(next<0||next>=students.length||turnStage?.classList.contains('book-transfer-stage'))return;
 if(!notebookInteractionLocked){runNotebookMotion(()=>flipNotebook(direction));return}
 // Close an open book before moving that whole book in either direction.
 if(bookPage!==0){
  if(!incoming&&motionEnabled())closeNotebookToLeft(next);
  else{
   showBookPage(0,()=>flipNotebook(direction));
   if(turnStage){turnStage.classList.add('book-transfer-stage');turnStage.dataset.closeDirection='right';}
  }
  return;
 }
 const source=incoming?$('.previous-book'):$('.notebook-cover');
 if(!source||!motionEnabled()){changeStudent(next);return}
 cancelPageTurn();togglePreferences(false);
 const root=$('#manuscript'),rootRect=root.getBoundingClientRect(),scale=rootRect.width/root.offsetWidth,w=sheet.width*scale,h=sheet.height*scale;
 const tilt=-2*Math.PI/180;
 // The adjacent book's right binding and active book's left binding are the
 // two endpoints of one hinge path. There is no independent airborne motion.
 const neighbourRect=$('.previous-book')?.getBoundingClientRect();
 const neighbourCenter=neighbourRect?{x:neighbourRect.left+neighbourRect.width/2,y:neighbourRect.top+neighbourRect.height/2}:{x:rootRect.left+(-125+sheet.width/2)*scale,y:rootRect.top+(9+sheet.height/2)*scale};
 const leftPivot={x:neighbourCenter.x+w/2*Math.cos(tilt),y:neighbourCenter.y+w/2*Math.sin(tilt)};
 const rightPivot={x:rootRect.right-w,y:rootRect.top+h/2};
 const start=incoming?leftPivot:rightPivot,end=incoming?rightPivot:leftPivot;
 const moveOriginal=incoming&&student===1;
 const sourceParent=source.parentNode,sourceSibling=source.nextSibling,sourceStyle=source.getAttribute('style');
 const sourcePaint=moveOriginal?snapshotProperties.map(k=>k+':'+getComputedStyle(source).getPropertyValue(k)).join(';'):'';
 const front=moveOriginal?document.createElement('div'):captureLeaf(source);
 if(moveOriginal)front.className='turn-leaf-original';
 const mountOriginal=()=>{
  if(!moveOriginal||front.contains(source))return;
  source.style.cssText=sourcePaint;
  Object.assign(source.style,{position:'absolute',left:'0',top:'0',width:sheet.width+'px',height:sheet.height+'px',margin:'0',transform:`scale(${scale})`,transformOrigin:'0 0',pointerEvents:'none'});
  front.append(source);
 };
 // Build only the reverse face as an inert measurement copy. Live paper and
 // student state are never swapped to prepare the animation.
 let target;
 if(incoming){
  const template=document.createElement('template');
  template.innerHTML=renderNotebook({questions:[0,1].map(i=>getDemoQuestion(settings.subject,next,i)),student:students[next],grades:[0,1].map(i=>getDemoGrade(settings.subject,next,i)),tools:''});
  target=template.content.querySelector('.notebook-cover');
 }else{
  target=document.createElement('div');target.className='adjacent-book previous-book';
  target.innerHTML='<span class="back-cover-binding" aria-hidden="true"></span>';
  Object.assign(target.style,{position:'relative',left:'0',top:'0',transform:'none'});
 }
 target.style.animation='none';
 const measure=document.createElement('div');measure.className='page-spread cover-spread';
 Object.assign(measure.style,{position:'absolute',left:(sheet.width*(bookStep()-1))+'px',top:'0',display:'block',width:sheet.width+'px',pointerEvents:'none'});
 measure.inert=true;measure.setAttribute('aria-hidden','true');measure.append(target);root.append(measure);
 const back=captureLeaf(target);measure.remove();
 const stage=document.createElement('div');stage.className='page-turn-stage book-transfer-stage';stage.dataset.direction=incoming?'right':'left';stage.dataset.sourceMode=moveOriginal?'original':'copy';stage.inert=true;stage.setAttribute('aria-hidden','true');
 // First park the current book in the tilted right pile. Only after it is
 // fully at rest may the previous book's copy begin its own flight.
 let underlay=null;
 if(incoming){
  const copy=captureLeaf($('.notebook-cover'));Object.assign(copy.style,{left:'0',top:'0',width:w+'px',height:h+'px'});copy.firstElementChild.style.transform=`scale(${scale})`;
  copy.querySelector('.paper-footer')?.remove();
  underlay=document.createElement('div');underlay.className='book-settle-copy book-underlay-copy';Object.assign(underlay.style,{width:w+'px',height:h+'px'});underlay.append(copy);stage.append(underlay);stage.dataset.phase='placing';
 }
 const flight=document.createElement('div');flight.className='book-transfer-copy';Object.assign(flight.style,{width:w+'px',height:h+'px',transformOrigin:incoming?'100% 50%':'0 50%'});
 for(const [copy,reverse] of [[front,false],[back,true]]){
  Object.assign(copy.style,{left:'0',top:'0',width:w+'px',height:h+'px'});
  if(copy.firstElementChild)copy.firstElementChild.style.transform=`scale(${scale})`;
  // Each snapshot is a single book; lower stack layers stay in the live pile.
  const face=document.createElement('div');face.className='book-transfer-face'+(reverse?' book-transfer-back':'');face.append(copy);flight.append(face);
 }
 const spine=document.createElement('div');spine.className='book-transfer-spine';Object.assign(spine.style,{width:Math.max(1,2*scale)+'px',left:incoming?'100%':'0'});flight.append(spine);
 stage.style.perspectiveOrigin=`${(start.x+end.x)/2}px ${(start.y+end.y)/2}px`;
 stage.append(flight);document.body.append(stage);turnStage=stage;
 // Lift the outgoing cover's copy to expose the tilted book underneath.
 // Hide its stationary source, restoring it on completion or interruption.
 const viewport=$('#paper-viewport');viewport.classList.add('book-leaving');
 const restore=()=>{
  if(moveOriginal&&front.contains(source)){
   sourceParent.insertBefore(source,sourceSibling?.parentNode===sourceParent?sourceSibling:null);
   if(sourceStyle===null)source.removeAttribute('style');else source.setAttribute('style',sourceStyle);
  }
  viewport.classList.remove('book-leaving');
 };
 let frame=0,startTime,phase=incoming?'placing':'flipping';
 const handle={cancel(){cancelAnimationFrame(frame);restore();stage.remove();}};turnAnimation=handle;
 function pose(p){
  const pivotX=start.x+(end.x-start.x)*p,pivotY=start.y+(end.y-start.y)*p;
  flight.style.transform=`translate3d(${pivotX-(incoming?w:0)}px,${pivotY-h/2}px,0) rotateZ(${-2*(incoming?1-p:p)}deg) rotateY(${(incoming?180:-180)*p}deg)`;
 }
 function park(p){
  underlay.style.transform=`translate(${rightPivot.x+nextBookPose.x*scale*p}px,${rootRect.top+(-h/5+nextBookPose.y*scale)*p}px) rotate(${nextBookPose.angle*p}deg)`;
 }
 function draw(now){
  if(startTime===undefined)startTime=now;
  if(phase==='placing'){
   const t=Math.min(1,((now-startTime)*motionRate())/650);park(t*t*(3-2*t));stage.dataset.progress=String(Math.round(t*100));
   if(t===1){phase='placed';stage.dataset.phase='placed';startTime=now;}
   frame=requestAnimationFrame(draw);return;
  }
  if(phase==='placed'){
   if(now-startTime>=120/motionRate()){phase='flipping';stage.dataset.phase='flipping';startTime=now;mountOriginal();flight.hidden=false;}
   frame=requestAnimationFrame(draw);return;
  }
  const t=Math.min(1,((now-startTime)*motionRate())/1150),motion=Math.min(1,t/.94),p=(1-Math.cos(Math.PI*motion))/2;
  pose(p);stage.dataset.progress=String(Math.round(p*100));
  if(t<1)frame=requestAnimationFrame(draw);
  else if(!incoming){settleNextNotebook(next,stage,restore);}
  else finishNotebookTransfer(next,stage,restore);
 }
 pose(0);if(underlay){park(0);flight.hidden=true;}frame=requestAnimationFrame(draw);
}
// Keep the pile stationary while a copy moves, except for the final notebook:
// there is no book beneath it, so move that original surface directly.
function settleNextNotebook(next,stage,restore){
 const source=$('.next-book'),root=$('#manuscript'),rect=root.getBoundingClientRect(),scale=rect.width/root.offsetWidth;
 if(!source){finishNotebookTransfer(next,stage,restore);return}
 const w=sheet.width*scale,h=sheet.height*scale,x=rect.right-w,y=rect.top;
 const last=next===students.length-1,originalStyle=source.getAttribute('style');
 let copy=null,sheetCopy=null;
 if(!last){
  copy=captureLeaf(source);Object.assign(copy.style,{left:'0',top:'0',width:w+'px',height:h+'px'});copy.firstElementChild.style.transform=`scale(${scale})`;
  sheetCopy=document.createElement('div');sheetCopy.className='book-settle-copy';Object.assign(sheetCopy.style,{width:w+'px',height:h+'px'});sheetCopy.append(copy);stage.append(sheetCopy);
 }
 stage.dataset.phase='straightening';stage.dataset.settleMode=last?'original':'copy';
 const label=(copy||source).querySelector('.book-edge-label'),labelOpacity=label?.style.opacity;let frame=0,startTime;
 const cleanup=()=>{if(last){if(originalStyle===null)source.removeAttribute('style');else source.setAttribute('style',originalStyle);if(label)label.style.opacity=labelOpacity;}restore();};
 const handle={cancel(){cancelAnimationFrame(frame);cleanup();stage.remove();}};turnAnimation=handle;
 function pose(p){
  if(last){source.style.left=(root.offsetWidth-sheet.width+nextBookPose.x*(1-p))+'px';source.style.top=((-sheet.height/5+nextBookPose.y)*(1-p))+'px';source.style.transform=`rotate(${nextBookPose.angle*(1-p)}deg)`;}
  else sheetCopy.style.transform=`translate(${x+nextBookPose.x*scale*(1-p)}px,${y+(-h/5+nextBookPose.y*scale)*(1-p)}px) rotate(${nextBookPose.angle*(1-p)}deg)`;
  if(label)label.style.opacity=String(1-p);
 }
 function draw(now){
  if(startTime===undefined)startTime=now;
  const t=Math.min(1,((now-startTime)*motionRate())/650),p=t*t*(3-2*t);pose(p);stage.dataset.progress=String(Math.round(p*100));
  if(t<1)frame=requestAnimationFrame(draw);
  else finishNotebookTransfer(next,stage,cleanup);
 }
 pose(0);frame=requestAnimationFrame(draw);
}
// Replace the landed copy and live paper atomically before the next paint.
// A crossfade would double their text/shadows and create a brightness flash.
function finishNotebookTransfer(next,stage,restore){
 restore();turnAnimation=null;turnStage=null;changeStudent(next);stage.remove();
}
function changeStudent(next){if(next<0||next>=students.length)return;cancelPageTurn();student=next;active=0;bookPage=0;render();window.scrollTo({top:0,behavior:'instant'})}
function bind(){
 const cover=$('[data-open-notebook]');
 const openCover=()=>{if(bookPage!==0||turnStage)return;requestLandscape();turnBook(1);};
 cover.onclick=openCover;cover.onkeydown=e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();openCover();}};
 const jump=$('#book-jump');jump.onchange=()=>{const n=Number(jump.value);if(Number.isInteger(n)&&n>=1&&n<=students.length){if(n-1!==student)changeStudent(n-1)}else jump.value=student+1;};jump.onkeydown=e=>{if(e.key==='Enter'){e.preventDefault();jump.onchange();}};
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
 $$('[data-next-student]').forEach(b=>{b.disabled=student===students.length-1;b.onclick=()=>flipNotebook(1)});
 $$('[data-action]').forEach(b=>b.onclick=()=>action(b.dataset.action));
 $$('[data-preset]').forEach(b=>b.onclick=()=>{settings=sanitize({...settings,...presets[b.dataset.preset],preset:b.dataset.preset,subject:settings.subject,marks:settings.marks,reading:settings.reading});apply()});
 $$('[data-ink]').forEach(b=>b.onclick=()=>{settings.ink=b.dataset.ink;apply()});
 $$('input[name=document-style]').forEach(el=>el.onchange=()=>{if(el.value!=='notebook')return;settings.documentStyle='notebook';apply()});
 $$('input[name=reading]').forEach(el=>el.onchange=()=>{settings.reading=el.value;apply()});
 $('#animations-enabled').onchange=e=>{settings.animations=e.target.checked;apply()};
 $$('input[name=motion-speed]').forEach(el=>el.onchange=()=>{settings.motionSpeed=el.value;apply()});
 $('#panel-font').onchange=e=>{settings.panelFont=e.target.value;apply()};
 $$('input[name=background]').forEach(el=>el.onchange=()=>{settings.background=el.value;apply()});
 $('#subject').onchange=e=>{settings.subject=e.target.value;active=0;render()};
 $('#preference-note').oninput=e=>{note=e.target.value;updateChoice();persist()};
}
// Fade only manuscript ink. Paper, ruling and the book binding are untouched.
function syncSettingsMask(){
 const panel=$('#preferences');if(!panel)return;
 const layers=$$('.paper-tools,.document-heading,.page-running,.original-answer,.grade-ink,.teacher-writing,.page-next,.paper-footer,.page-edge-turn,.submission-end,.cover-print',$('#manuscript'));
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
function action(name){if(name==='previous-student')flipNotebook(-1);else if(name==='next-student')flipNotebook(1);else if(name==='preferences')togglePreferences();else if(name==='close-preferences')togglePreferences(false);else if(name==='toggle-zoom'){toggleFullscreen()}else if(name==='toggle-marks'){settings.marks=!settings.marks;apply()}else if(name==='reset-style'){settings=sanitize({documentStyle:'notebook',preset:settings.preset,subject:settings.subject,reading:'double'});apply()}else if(name==='save-candidate'){if(candidates.length>=4)return;candidates.push({id:Date.now().toString(36),settings:{...settings}});persist();renderCandidates();announce(storageOK?'候选已保存在当前浏览器。':'候选仅暂存在当前页面，请下载备份。')}else if(name==='confirm-choice'){togglePreferences(true);$('#choice-section').hidden=false;confirmed={settings:{...settings},note,at:new Date().toISOString()};updateChoice();persist();smoothTo($('#choice-section'))}else if(name==='copy-choice')copyChoice();else if(name==='download-choice')downloadChoice()}
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
 const sceneWidth=width+420,sceneHeight=height+280;
 const availableWidth=Math.max(1,document.documentElement.clientWidth-48);
 const availableHeight=Math.max(1,window.innerHeight-80);
 const scale=Math.min(availableWidth/sceneWidth,availableHeight/sceneHeight);
 viewport.style.setProperty('--scene-scale',scale);
 viewport.style.setProperty('--book-left',(16+150*scale)+'px');
 viewport.style.setProperty('--book-top',(16+230*scale)+'px');
 viewport.style.setProperty('--book-right',(16+270*scale)+'px');
 viewport.style.setProperty('--book-bottom',(16+50*scale)+'px');
 viewport.style.setProperty('--stack-next-left',(width-sheet.width+nextBookPose.x)+'px');
 viewport.style.setProperty('--stack-next-angle',nextBookPose.angle+'deg');
 // Shared pose keeps the idle book and both animation endpoints aligned.
 viewport.style.setProperty('--stack-next-top',(-height/5+nextBookPose.y)+'px');
 root.style.setProperty('--sheet-width',sheet.width+'px');root.style.setProperty('--sheet-height',height+'px');
 root.style.setProperty('--canvas-width',width+'px');root.style.setProperty('--view-scale',scale);
 viewport.style.width=(sceneWidth*scale+32)+'px';viewport.style.height=(sceneHeight*scale+32)+'px';
 root.dataset.displayScale=scale.toFixed(4);
 // Anchor the UI to the stationary paper surface, not the browser viewport.
 // Keep it legible at normal sizes and fit it inside even a small cover leaf.
 const inset=20*scale,uiScale=Math.min(1,(sheet.width*scale-2*inset)/370);
 viewport.style.setProperty('--paper-inset',(16+270*scale+inset)+'px');
 viewport.style.setProperty('--paper-tools-top',(16+230*scale+inset)+'px');
 viewport.style.setProperty('--paper-ui-scale',uiScale);
 viewport.style.setProperty('--paper-settings-top',(16+230*scale+inset+54*uiScale)+'px');
 viewport.style.setProperty('--paper-settings-height',Math.max(0,(height*scale-2*inset-54*uiScale)/uiScale)+'px');
}
async function toggleFullscreen(){
 try{if(document.fullscreenElement)await document.exitFullscreen();else if(document.documentElement.requestFullscreen)await document.documentElement.requestFullscreen();else $('#reader-status').textContent='当前浏览器不支持全屏，请使用浏览器的全屏功能。';}
 catch{$('#reader-status').textContent='未能进入全屏，请使用浏览器的全屏功能。';}
}
document.addEventListener('fullscreenchange',()=>{fitPaper();const b=$('#zoom');if(b){const label=document.fullscreenElement?'退出全屏':'全屏';b.setAttribute('aria-pressed',Boolean(document.fullscreenElement));b.setAttribute('aria-label',label);b.dataset.tip=label;}});
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
