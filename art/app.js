import {unlockVault,loadAsset,shanghaiDate} from './crypto.js';
const $=id=>document.getElementById(id);
let opened=null,controller=null,generation=0,urls=[],musicPromise=null,videoPromise=null;
function message(id,text,error=false){$(id).textContent=text;$(id).classList.toggle('error',error);}
function url(blob){const value=URL.createObjectURL(blob);urls.push(value);return value;}
function lock(expired=false){
  generation++;controller?.abort();controller=null;opened=null;musicPromise=null;videoPromise=null;
  for(const id of ['video','audio']){$(id).pause();$(id).removeAttribute('src');$(id).load();}
  $('video').controls=false;$('video').removeAttribute('poster');urls.forEach(x=>URL.revokeObjectURL(x));urls=[];
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
    const r=await fetch('vault.json');if(!r.ok)throw new Error('页面加载失败，请重试。');
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
  if(!musicPromise){const current=generation;musicPromise=loadAsset(opened.manifest.assets.music,opened.key,p=>message('music-status',`音乐加载中 · ${Math.round(p*100)}%`),controller.signal).then(blob=>{if(current!==generation)throw new DOMException('Aborted','AbortError');message('music-status','');return url(blob);}).catch(e=>{musicPromise=null;throw e;});}return musicPromise;
}
$('play').addEventListener('click',async()=>{
  if(!opened)return;const current=generation;$('play').disabled=true;
  try{if(!videoPromise)videoPromise=loadAsset(opened.manifest.assets.movie,opened.key,p=>message('video-status',`MV 加载中 · ${Math.round(p*100)}%`),controller.signal).then(blob=>{if(current!==generation)throw new DOMException('Aborted','AbortError');return url(blob);}).catch(e=>{videoPromise=null;throw e;});
    const source=await videoPromise;if(current!==generation)return;$('video').src=source;$('video').controls=true;$('play').hidden=true;message('video-status','');await $('video').play();
  }catch(e){if(current!==generation||e.name==='AbortError')return;message('video-status',e.name==='NotAllowedError'?'点击视频播放按钮继续。':e.message,true);}
  finally{if(current===generation)$('play').disabled=false;}
});
$('listen').addEventListener('click',async()=>{
  $('listen').disabled=true;const current=generation;try{const source=await music();if(current!==generation)return;$('audio').src=source;$('audio').hidden=false;$('listen').hidden=true;await $('audio').play();}catch(e){if(current===generation&&e.name!=='AbortError')message('music-status',e.name==='NotAllowedError'?'点击音频播放按钮继续。':e.message,true);}finally{if(current===generation)$('listen').disabled=false;}
});
$('download').addEventListener('click',async()=>{
  $('download').disabled=true;const current=generation;try{const source=await music();if(current!==generation)return;const a=document.createElement('a');a.href=source;a.download=opened.manifest.assets.music.filename;document.body.append(a);a.click();a.remove();}catch(e){if(current===generation&&e.name!=='AbortError')message('music-status',e.message,true);}finally{if(current===generation)$('download').disabled=false;}
});
window.addEventListener('pagehide',()=>lock());
