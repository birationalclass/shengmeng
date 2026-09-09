// Motion belongs to the notebook accordions; diagram timelines stay independent.
export function createNotebookMotion({language}) {
 const storageKey='spectral-notebook-motion',defaults={effect:'soft',duration:900};
 const reduced=matchMedia('(prefers-reduced-motion:reduce)'),records=new WeakMap(),running=new Map();
 let settings={...defaults},previewOpen=true;
 try {const saved=JSON.parse(localStorage.getItem(storageKey));if(['soft','slide','none'].includes(saved?.effect))settings.effect=saved.effect;if(Number.isFinite(saved?.duration))settings.duration=Math.min(1800,Math.max(300,saved.duration));} catch {}
 const $=s=>document.querySelector(s),dialog=$('#motionSettings'),button=$('#settingsButton'),effect=$('#motionEffect'),duration=$('#motionDuration'),preview=$('#motionPreviewBody');
 // Measure content independently of the animated outer height. In particular,
 // math/font transitions can keep changing its natural height during a fold.
 function naturalHeight(body){
  const rect=body.getBoundingClientRect(),style=getComputedStyle(body),children=[...body.children].filter(el=>el.getClientRects().length);
  if(!children.length)return 0;
  return Math.max(...children.map(el=>el.getBoundingClientRect().bottom-rect.top+parseFloat(getComputedStyle(el).marginBottom||0)))+parseFloat(style.paddingBottom||0)+parseFloat(style.borderBottomWidth||0);
 }
 const t=(zh,en)=>language()==='en'?en:zh;
 const milliseconds=()=>reduced.matches||settings.effect==='none'?0:settings.duration;
 function settleAll(){for(const finish of [...running.values()])finish();}
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
  if(!previous||immediate||!ms||!body.getClientRects().length||Math.abs(from-to)<1){finish();return;}
  body.classList.add('accordion-moving');
  const soft=settings.effect==='soft',animation=body.animate([{height:from+'px',opacity:soft?opacity:1},{height:to+'px',opacity:soft?(open?1:0):1}],{duration:ms,easing:'cubic-bezier(.33,0,.2,1)',fill:'both'});
  animation.id='notebook-fold';record.animation=animation;running.set(body,finish);animation.onfinish=finish;
  const end=performance.now()+ms;let target=to;
  const follow=()=>{
   if(records.get(body)!==record||animation.playState==='finished')return;
   const next=open?naturalHeight(body):0;
   if(Math.abs(next-target)>.25){
    const now=getComputedStyle(body),height=body.getBoundingClientRect().height,remaining=Math.max(1,end-performance.now());
    animation.effect.setKeyframes([{height:height+'px',opacity:soft?now.opacity:1},{height:next+'px',opacity:soft?(open?1:0):1}]);
    animation.effect.updateTiming({duration:remaining});animation.currentTime=0;target=next;
   }
   record.frame=requestAnimationFrame(follow);
  };record.frame=requestAnimationFrame(follow);
 }
 function sync() {
  const off=!milliseconds();document.documentElement.dataset.notebookMotion=off?'none':settings.effect;document.documentElement.style.setProperty('--notebook-motion-time',(off?0:settings.duration)+'ms');
  button.setAttribute('aria-label',t('动画设置','Animation settings'));button.title=t('动画设置','Animation settings');
  $('#motionTitle').textContent=t('动画设置','Animation settings');$('#closeMotionSettings').setAttribute('aria-label',t('关闭设置','Close settings'));
  $('#motionScope').textContent=t('左侧定义、命题与定理卡片','Definition, proposition and theorem cards');
  $('#motionEffectLabel').textContent=t('收放效果','Accordion effect');
  for(const [value,zh,en] of [['soft','柔和收放','Slide and fade'],['slide','简洁收放','Slide only'],['none','关闭动画','No animation']])effect.querySelector(`[value="${value}"]`).textContent=t(zh,en);
  effect.value=settings.effect;duration.value=settings.duration;duration.disabled=settings.effect==='none'||reduced.matches;
  $('#motionDurationLabel').textContent=t('收放时长','Duration');$('#motionDurationValue').textContent=(settings.duration/1000).toFixed(1)+t(' 秒',' s');
  $('#motionReduced').hidden=!reduced.matches;$('#motionReduced').textContent=t('遵循系统的“减弱动态效果”设置。','Following your system’s reduced-motion preference.');
  $('#motionPreviewTitle').textContent=t('预览','Preview');$('#motionPreviewText').textContent=t('展开与收起保持连续，内容随卡片平缓呈现。','Content opens and closes in one continuous motion.');
  $('#motionPreviewToggle').textContent=previewOpen?t('收起预览','Collapse preview'):t('展开预览','Expand preview');$('#motionPreviewToggle').setAttribute('aria-expanded',String(previewOpen));
  $('#motionReset').textContent=t('恢复默认','Restore defaults');$('#motionSaved').textContent=t('自动保存到此浏览器','Saved in this browser');
 }
 function update(){settleAll();settings={effect:effect.value,duration:Number(duration.value)};try{localStorage.setItem(storageKey,JSON.stringify(settings));}catch{}sync();}
 effect.addEventListener('change',update);duration.addEventListener('input',update);
 $('#motionReset').onclick=()=>{effect.value=defaults.effect;duration.value=defaults.duration;update();};
 $('#motionPreviewToggle').onclick=()=>{previewOpen=!previewOpen;setExpanded(preview,previewOpen);sync();};
 button.onclick=()=>{sync();dialog.showModal();};$('#closeMotionSettings').onclick=()=>dialog.close();
 dialog.addEventListener('close',()=>{settleAll();button.focus({preventScroll:true});});
 reduced.addEventListener('change',()=>{settleAll();sync();});
 let lastWidth=0;new ResizeObserver(entries=>{const width=entries[0].contentRect.width;if(lastWidth&&Math.abs(lastWidth-width)>1)settleAll();lastWidth=width;}).observe($('.explanation'));
 setExpanded(preview,true,{immediate:true});sync();
 return {setExpanded,sync,settleAll,duration:milliseconds};
}
