// Motion belongs to the notebook accordions; diagram timelines stay independent.
export function createNotebookMotion({language}) {
 const storageKey='spectral-notebook-motion',defaults={effect:'soft',duration:900,autoCollapse:false};
 const reduced=matchMedia('(prefers-reduced-motion:reduce)'),records=new WeakMap(),running=new Map();
 let settings={...defaults},previewOpen=true,opener=null;
 try {const saved=JSON.parse(localStorage.getItem(storageKey));if(typeof saved?.autoCollapse==='boolean')settings.autoCollapse=saved.autoCollapse;if(['soft','slide','none'].includes(saved?.effect))settings.effect=saved.effect;if(Number.isFinite(saved?.duration))settings.duration=Math.min(1800,Math.max(300,saved.duration));} catch {}
 const $=s=>document.querySelector(s),dialog=$('#motionSettings'),button=$('#settingsButton'),effect=$('#motionEffect'),autoCollapse=$('#motionAutoCollapse'),duration=$('#motionDuration'),preview=$('#motionPreviewBody');
 // Measure content independently of the animated outer height. In particular,
 // math/font transitions can keep changing its natural height during a fold.
 function naturalHeight(body){
  const rect=body.getBoundingClientRect(),style=getComputedStyle(body),children=[...body.children].filter(el=>el.getClientRects().length);
  if(!children.length)return 0;
  return Math.max(...children.map(el=>el.getBoundingClientRect().bottom-rect.top+parseFloat(getComputedStyle(el).marginBottom||0)))+parseFloat(style.paddingBottom||0)+parseFloat(style.borderBottomWidth||0);
 }
 // Every opening reserves 70% for geometry, then 30% for content.
 const phases=ms=>({frame:ms*.7,content:ms*.3});
 const t=(zh,en)=>language()==='en'?en:zh;
 const milliseconds=()=>reduced.matches||settings.effect==='none'?0:settings.duration;
 function settleAll(){for(const finish of [...running.values()])finish();}
 // A new card uses the same frame-before-content sequence as an accordion.
 // The holding animations prevent even a single frame of stretched text.
 function revealCard(card){
  running.get(card)?.();
  const ms=milliseconds();if(!ms||!card?.getClientRects().length)return;
  const {frame,content}=phases(ms),children=[...card.children];
  const holds=children.map(el=>el.animate([{opacity:0},{opacity:0}],{duration:1,fill:'both'}));
  holds.forEach(a=>a.id='notebook-content-hold');
  const animation=card.animate([
   {opacity:.3,transform:`scale(${2/card.offsetWidth},${2/card.offsetHeight})`,transformOrigin:'0 0'},
   {opacity:1,transform:'scale(1)',transformOrigin:'0 0'}
  ],{duration:frame,easing:'cubic-bezier(.33,0,.2,1)',fill:'both'});
  animation.id='notebook-frame';
  const effects=[animation,...holds];
  const finish=()=>{effects.forEach(a=>{a.onfinish=null;a.cancel();});running.delete(card);};
  running.set(card,finish);
  animation.onfinish=()=>{
   // Start the fade from completion, never from an overlapping guessed delay.
   animation.onfinish=null;animation.cancel();
   const fades=children.map(el=>{const a=el.animate([{opacity:0},{opacity:1}],{duration:content,easing:'ease-out',fill:'both'});a.id='notebook-content-in';return a;});
   effects.push(...fades);holds.forEach(a=>a.cancel());
   Promise.all(fades.map(a=>a.finished)).then(()=>{if(running.get(card)===finish)finish();},()=>{});
  };
 }
 function setExpanded(body,open,{immediate=false}={}) {
  if(!body)return;
  const previous=records.get(body);
  if(previous?.open===open){if(immediate)running.get(body)?.();return;}
  const from=body.hidden?0:body.getBoundingClientRect().height,opacity=body.hidden?0:Number(getComputedStyle(body).opacity);
  if(previous?.animation){cancelAnimationFrame(previous.frame);previous.animation.onfinish=null;previous.animation.cancel();running.delete(body);}
  const record={open,animation:null,frame:0};records.set(body,record);
  body.hidden=false;body.inert=!open;body.classList.remove('accordion-moving');
  const natural=naturalHeight(body),to=open?natural:0,ms=milliseconds();
  const finish=()=>{if(records.get(body)!==record)return;cancelAnimationFrame(record.frame);body.hidden=!open;body.classList.remove('accordion-moving');if(record.animation){record.animation.onfinish=null;record.animation.cancel();record.animation=null;}running.delete(body);};
  if(!previous||immediate||!ms||!body.getClientRects().length){finish();return;}
  body.classList.add('accordion-moving');running.set(body,finish);
  const {frame,content}=phases(ms),soft=settings.effect==='soft';
  const fadeIn=()=>{
   cancelAnimationFrame(record.frame);
   const old=record.animation;
   // Create the replacement before removing the opaque hold: no text flash.
   const fade=body.animate([{opacity:0},{opacity:1}],{duration:content,easing:'ease-out',fill:'both'});
   fade.id='notebook-content-in';record.animation=fade;
   if(old){old.onfinish=null;old.cancel();}fade.onfinish=finish;
  };
  const geometryMs=open?frame:ms;
  // Opening height never carries visible content. Closing may fade as before.
  const frames=(height,target,currentOpacity)=>[
   {height:height+'px',opacity:open?0:soft?currentOpacity:1},
   {height:target+'px',opacity:open?0:soft?0:1}
  ];
  const animation=body.animate(frames(from,to,opacity),{duration:geometryMs,easing:'cubic-bezier(.33,0,.2,1)',fill:'both'});
  animation.id='notebook-fold';record.animation=animation;animation.onfinish=open?fadeIn:finish;
  const end=performance.now()+geometryMs;let target=to;
  const follow=()=>{
   if(records.get(body)!==record||record.animation!==animation||animation.playState==='finished')return;
   const next=open?naturalHeight(body):0;
   if(Math.abs(next-target)>.25){
    const now=getComputedStyle(body),height=body.getBoundingClientRect().height,remaining=Math.max(1,end-performance.now());
    animation.effect.setKeyframes(frames(height,next,Number(now.opacity)));
    animation.effect.updateTiming({duration:remaining});animation.currentTime=0;target=next;
   }
   record.frame=requestAnimationFrame(follow);
  };record.frame=requestAnimationFrame(follow);
 }
 function sync() {
  window.spectralPanelStyle?.sync();
  const off=!milliseconds();document.documentElement.dataset.notebookMotion=off?'none':settings.effect;document.documentElement.style.setProperty('--notebook-motion-time',(off?0:settings.duration)+'ms');
  button.setAttribute('aria-label',t('显示设置','Display settings'));button.title=t('显示设置','Display settings');
  $('#motionTitle').textContent=t('显示设置','Display settings');$('#closeMotionSettings').setAttribute('aria-label',t('关闭设置','Close settings'));
  $('#coverFontLabel').textContent=t('中文标题风格','Chinese title style');
  $('#coverStyleA').textContent=t('A · 清雅宋体','A · Editorial serif');$('#coverStyleC').textContent=t('C · 书法风格','C · Calligraphy');
  $('#coverFontHint').textContent=t('调整中文标题字体，英文设计保持不变。','Changes Chinese title typography. The English design stays the same.');
  for(const radio of document.querySelectorAll('[name="coverFont"]'))radio.checked=radio.value===(window.spectralCover?.style()||'c');
  $('#motionScope').textContent=t('左侧定义、命题与定理卡片','Definition, proposition and theorem cards');
  $('#motionAutoCollapseLabel').textContent=t('自动折叠','Auto-collapse');autoCollapse.checked=settings.autoCollapse;
  $('#motionAutoCollapseHint').textContent=t('显示下一条时收起此前内容；默认关闭。','Fold earlier content when advancing to the next entry. Off by default.');
  $('#motionEffectLabel').textContent=t('收起效果','Collapse effect');
  for(const [value,zh,en] of [['soft','柔和收起','Slide and fade'],['slide','简洁收起','Slide only'],['none','关闭动画','No animation']])effect.querySelector(`[value="${value}"]`).textContent=t(zh,en);
  effect.value=settings.effect;duration.value=settings.duration;duration.disabled=settings.effect==='none'||reduced.matches;
  $('#motionDurationLabel').textContent=t('收放时长','Duration');$('#motionDurationValue').textContent=(settings.duration/1000).toFixed(1)+t(' 秒',' s');
  $('#motionReduced').hidden=!reduced.matches;$('#motionReduced').textContent=t('遵循系统的“减弱动态效果”设置。','Following your system’s reduced-motion preference.');
  $('#motionPreviewTitle').textContent=t('预览','Preview');$('#motionPreviewText').textContent=t('展开时，方框先完成延展，文字与公式随后淡入。','On opening, the frame expands fully before text and formulas fade in.');
  $('#motionPreviewToggle').textContent=previewOpen?t('收起预览','Collapse preview'):t('展开预览','Expand preview');$('#motionPreviewToggle').setAttribute('aria-expanded',String(previewOpen));
  $('#motionReset').textContent=t('恢复默认','Restore defaults');$('#motionSaved').textContent=t('自动保存到此浏览器','Saved in this browser');
 }
 function update(){settleAll();settings={effect:effect.value,duration:Number(duration.value),autoCollapse:autoCollapse.checked};try{localStorage.setItem(storageKey,JSON.stringify(settings));}catch{}sync();}
 autoCollapse.addEventListener('change',update);effect.addEventListener('change',update);duration.addEventListener('input',update);
 $('#motionReset').onclick=()=>{effect.value=defaults.effect;duration.value=defaults.duration;autoCollapse.checked=defaults.autoCollapse;window.spectralCover?.setStyle('c');window.spectralPanelStyle?.reset();update();};
 for(const radio of document.querySelectorAll('[name="coverFont"]'))radio.addEventListener('change',()=>{if(radio.checked){window.spectralCover?.setStyle(radio.value);sync();}});
 $('#motionPreviewToggle').onclick=()=>{previewOpen=!previewOpen;setExpanded(preview,previewOpen);sync();};
 button.onclick=$('#coverSettings').onclick=event=>{opener=event.currentTarget;sync();dialog.showModal();};$('#coverSettings').disabled=false;$('#closeMotionSettings').onclick=()=>dialog.close();
 dialog.addEventListener('close',()=>{settleAll();(opener||button).focus({preventScroll:true});});
 reduced.addEventListener('change',()=>{settleAll();sync();});
 // Settle outside the observer delivery: cancellation changes card heights.
 let lastWidth=0,resizeFrame=0;new ResizeObserver(entries=>{
  const width=entries[0].contentRect.width;
  if(lastWidth&&Math.abs(lastWidth-width)>1){cancelAnimationFrame(resizeFrame);resizeFrame=requestAnimationFrame(settleAll);}
  lastWidth=width;
 }).observe($('.explanation'));
 setExpanded(preview,true,{immediate:true});sync();
 return {setExpanded,revealCard,sync,settleAll,isAnimating:()=>running.size>0,duration:milliseconds,autoCollapse:()=>settings.autoCollapse};
}
