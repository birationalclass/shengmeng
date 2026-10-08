import {unlockVault,loadAsset,shanghaiDate} from './crypto.js?v=20261009-stream3';
import {SegmentedVideo,playerControls} from './stream.js?v=20261009-stream3';
const $=id=>document.getElementById(id);
let opened=null,controller=null,generation=0,urls=[],musicPromise=null,videoPromise=null,privateStream=null;
function message(id,text,error=false){$(id).textContent=text;$(id).classList.toggle('error',error);}
function url(blob){const value=URL.createObjectURL(blob);urls.push(value);return value;}
function lock(expired=false){
  generation++;privateStream?.destroy();privateStream=null;controller?.abort();controller=null;opened=null;musicPromise=null;videoPromise=null;
  for(const id of ['video','audio']){$(id).pause();$(id).removeAttribute('src');$(id).load();}
  $('video').controls=false;$('video-controls').hidden=true;$('video').removeAttribute('poster');urls.forEach(x=>URL.revokeObjectURL(x));urls=[];
  $('gallery').hidden=true;$('gate').hidden=false;$('lock').hidden=true;$('play').hidden=false;$('audio').hidden=true;$('listen').hidden=false;
  for(const id of ['play','listen','download','unlock'])$(id).disabled=false;
  message('video-status','');message('music-status','');message('gate-error',expired?'日期已更新，请重新输入访问密码。':'');$('password').value='';$('password').focus();
}
function checkDate(){if(opened&&opened.stamp!==shanghaiDate().stamp)lock(true);}
setInterval(checkDate,30000);document.addEventListener('visibilitychange',checkDate);$('lock').addEventListener('click',()=>lock());
$('unlock-form').addEventListener('submit',async event=>{
  event.preventDefault();const password=$('password').value;$('unlock').disabled=true;message('gate-error','正在打开…');
  const current=++generation;
  try{
    const r=await fetch('vault.json',{cache:'no-store'});if(!r.ok)throw new Error('页面加载失败，请重试。');
    const unlocked=await unlockVault(password,await r.json());if(current!==generation)return;
    opened=unlocked;controller=new AbortController();$('password').value='';$('work-title').textContent=opened.manifest.title;
    $('gate').hidden=true;$('gallery').hidden=false;$('lock').hidden=false;message('gate-error','');
    const poster=await loadAsset(opened.manifest.assets.poster,opened.key,()=>{},controller.signal);
    if(current!==generation)return;$('video').poster=url(poster);$('play').focus();
  }catch(error){if(current!==generation||error.name==='AbortError')return;if(opened)lock();message('gate-error',error.message||'无法打开，请重试。',true);$('password').focus();}
  finally{if(current===generation)$('unlock').disabled=false;}
});
async function music(){
  if(!opened)throw new Error('请先输入访问密码。');
  if(!musicPromise){message('music-status','音乐加载中 · 0%');const current=generation;musicPromise=loadAsset(opened.manifest.assets.music,opened.key,p=>message('music-status',`音乐加载中 · ${Math.round(p*100)}%`),controller.signal).then(blob=>{if(current!==generation)throw new DOMException('Aborted','AbortError');message('music-status','');return url(blob);}).catch(e=>{musicPromise=null;throw e;});}return musicPromise;
}
playerControls($('video'),$('video-controls'));
$('play').addEventListener('click',async()=>{
  if(!opened)return;const current=generation;$('play').disabled=true;message('video-status','正在准备播放…');
  try{
    $('public-video').pause();
    if(!privateStream){privateStream=new SegmentedVideo($('video'),opened.manifest.assets.creditStream,opened.key,controller.signal,(t,error)=>message('video-status',t,error));await privateStream.open();}
    if(current!==generation)return;
    $('play').hidden=true;$('video-controls').hidden=false;message('video-status','');await $('video').play();
  }catch(e){if(current!==generation||e.name==='AbortError')return;privateStream?.destroy();privateStream=null;$('play').hidden=false;message('video-status',e.name==='NotAllowedError'?'点击播放按钮继续。':e.message,true);}
  finally{if(current===generation)$('play').disabled=false;}
});
let publicStream=null;
const publicController=new AbortController();
playerControls($('public-video'),$('public-controls'));
$('public-play').addEventListener('click',async()=>{
  $('public-play').disabled=true;message('public-status','正在准备播放…');
  try {
    $('video').pause();$('audio').pause();
    if(!publicStream){
      const r=await fetch('qin-stream.json?v=20261009-v4');if(!r.ok)throw new Error('视频加载失败，请重试。');
      publicStream=new SegmentedVideo($('public-video'),await r.json(),null,publicController.signal,(t,error)=>message('public-status',t,error));await publicStream.open();
    }
    $('public-play').hidden=true;$('public-controls').hidden=false;message('public-status','');await $('public-video').play();
  }catch(e){publicStream?.destroy();publicStream=null;$('public-play').hidden=false;message('public-status',e.name==='NotAllowedError'?'点击播放按钮继续。':e.message,true);}
  finally{$('public-play').disabled=false;}
});
$('listen').addEventListener('click',async()=>{
  $('listen').disabled=true;const current=generation;try{const source=await music();if(current!==generation)return;$('audio').src=source;$('audio').hidden=false;$('listen').hidden=true;await $('audio').play();}catch(e){if(current===generation&&e.name!=='AbortError')message('music-status',e.name==='NotAllowedError'?'点击音频播放按钮继续。':e.message,true);}finally{if(current===generation)$('listen').disabled=false;}
});
$('download').addEventListener('click',async()=>{
  $('download').disabled=true;const current=generation;try{const source=await music();if(current!==generation)return;const a=document.createElement('a');a.href=source;a.download=opened.manifest.assets.music.filename;document.body.append(a);a.click();a.remove();}catch(e){if(current===generation&&e.name!=='AbortError')message('music-status',e.message,true);}finally{if(current===generation)$('download').disabled=false;}
});
window.addEventListener('pagehide',()=>{publicController.abort();lock();});
