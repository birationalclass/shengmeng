const $=id=>document.getElementById(id);
const panels=[['settingsButton','settings','settingsClose'],['viewButton','viewPanel','viewClose'],['exportButton','exportPanel','exportClose']];
let openPanel=null;
function closePanels(returnFocus=false){
 const previous=openPanel;
 for(const [button,panel] of panels){$(button).setAttribute('aria-expanded','false');$(panel).hidden=true;}
 openPanel=null;if(returnFocus&&previous)$(previous[0]).focus();
}
for(const entry of panels){const [button,panel,close]=entry;
 $(button).onclick=()=>{const wasOpen=openPanel===entry;closePanels();if(!wasOpen){openPanel=entry;$(button).setAttribute('aria-expanded','true');$(panel).hidden=false;$(close).focus();}};
 $(close).onclick=()=>closePanels(true);
}
document.addEventListener('pointerdown',e=>{if(openPanel&&!$(openPanel[1]).contains(e.target)&&!$(openPanel[0]).contains(e.target))closePanels();});
function setUI(hidden){closePanels();document.body.classList.toggle('ui-hidden',hidden);for(const node of document.querySelectorAll('.chrome')){node.inert=hidden;if(hidden)node.setAttribute('aria-hidden','true');else node.removeAttribute('aria-hidden');}$('showUI').hidden=!hidden;(hidden?$('showUI'):$('hideUI')).focus();}
$('hideUI').onclick=()=>setUI(true);$('showUI').onclick=()=>setUI(false);
document.addEventListener('keydown',e=>{
 const editing=e.target.matches('input,select,textarea,[contenteditable="true"]');
 if(e.key==='Escape'){if(openPanel){e.preventDefault();closePanels(true);}else if(document.body.classList.contains('ui-hidden'))setUI(false);}
 if(!editing&&e.key.toLowerCase()==='h'&&!e.ctrlKey&&!e.metaKey&&!e.altKey){e.preventDefault();setUI(!document.body.classList.contains('ui-hidden'));}
});
try{
 const studio=await import('./engine/studio.js?v=16');
 // Fullscreen includes the controls, so playback and settings stay accessible.
 $('fullscreen').onclick=async()=>{try{if(document.fullscreenElement)await document.exitFullscreen();else await document.documentElement.requestFullscreen();}catch{$('notice').hidden=false;$('notice').textContent='当前环境不支持全屏。';}};
 document.addEventListener('fullscreenchange',()=>{$('fullscreen').setAttribute('aria-pressed',String(!!document.fullscreenElement));});
 let quality='balanced';try{quality=localStorage.getItem('calligraphy-quality')||quality;}catch{}
 if(!['draft','balanced','high'].includes(quality))quality='balanced';$('quality').value=quality;studio.setQuality(quality);
 $('quality').onchange=e=>{studio.setQuality(e.target.value);try{localStorage.setItem('calligraphy-quality',e.target.value);}catch{}};
 let previousBackground='';
 function sync(){const state=studio.studioState();
  if(state.settings.background!==previousBackground){document.body.classList.toggle('dark',state.settings.background==='dark');previousBackground=state.settings.background;}
  $('pause').dataset.tip=$('pause').getAttribute('aria-label');
  $('view-label').textContent=state.building?'正在构形':!state.text?'':state.paused&&state.time>=state.duration?'成字':'立体书写';
 }
 sync();setInterval(sync,240);
}catch(error){
 $('loading').hidden=true;$('notice').hidden=false;$('notice').textContent='三维画面未能启动。请确认浏览器已开启 WebGL，然后刷新。';
 console.error(error);
}
