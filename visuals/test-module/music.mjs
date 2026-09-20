import {SOUNDTRACK_URL,SOUNDTRACK_TITLE} from './soundtrack.mjs?v=20260920audio1';
export function setupMusic({getPlaying,getTime}){
 const audio=document.createElement('audio');audio.id='soundtrack';audio.preload='metadata';audio.loop=true;audio.volume=.35;audio.muted=true;document.body.append(audio);
 const file=document.getElementById('musicFile'),toggle=document.getElementById('musicToggle'),volume=document.getElementById('musicVolume'),status=document.getElementById('musicStatus');let enabled=Boolean(SOUNDTRACK_URL),objectURL=null,awaitingGesture=false;
 const testMuted=new URLSearchParams(location.search).get('mute')==='1';
 function refresh(){toggle.textContent=enabled?'关闭背景音乐':'开启背景音乐';toggle.disabled=!audio.getAttribute('src');status.textContent=audio.getAttribute('src')?SOUNDTRACK_TITLE:'请导入未加密的 MP3、M4A、WAV 或 FLAC。';}
 async function sync(){audio.muted=testMuted||!enabled;if(enabled&&getPlaying()&&!testMuted){try{await audio.play();awaitingGesture=false;refresh();}catch(error){if(error.name==='NotAllowedError'&&enabled){awaitingGesture=true;status.textContent='背景音乐已开启，点击页面后开始播放。';}}}else audio.pause();}
 function seek(){if(Number.isFinite(audio.duration)&&audio.duration>0)audio.currentTime=getTime()%audio.duration;}
 if(SOUNDTRACK_URL)audio.src=SOUNDTRACK_URL;
 function unlock(){if(awaitingGesture&&enabled&&getPlaying()&&!testMuted&&!document.hidden){seek();sync();}}
 document.addEventListener('click',unlock);document.addEventListener('keydown',unlock);
 file.addEventListener('change',()=>{const selected=file.files?.[0];if(!selected)return;if(/\.(mflac|qmc\w*|mgg)$/i.test(selected.name)){status.textContent='这是加密音乐缓存，请改用未加密的音频文件。';file.value='';return;}if(objectURL)URL.revokeObjectURL(objectURL);objectURL=URL.createObjectURL(selected);audio.src=objectURL;enabled=false;refresh();});
 toggle.addEventListener('click',()=>{enabled=!enabled;seek();refresh();sync();});volume.addEventListener('input',()=>audio.volume=Number(volume.value)/100);audio.addEventListener('loadedmetadata',seek);audio.addEventListener('error',()=>{enabled=false;audio.pause();status.textContent='此文件无法播放，请选择未加密的 MP3、M4A、WAV 或 FLAC。';toggle.textContent='开启背景音乐';});
 refresh();return {sync,seek,audio};
}
