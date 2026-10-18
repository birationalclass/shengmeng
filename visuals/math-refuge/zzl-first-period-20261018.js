import {boardWaitAt,countdownTextRect,containsCountdown} from './board-countdown.js';
import {MIN_BOARD_REVIEW_SECONDS} from './board-review.js';
import {prepareClassroomAudioBlob,classroomAudioDecodeState} from './classroom-audio-decode.js?v=mp3-predecode-1';
import {prepareBoard,paintPrepared} from './zzl-first-period-renderer-20261018.js?v=mali-ready-1';
import {selectClassroomOpening,openingPeriod,classroomAudioRate,classroomDuration} from './classroom-opening.js?v=classroom-clarity-20261017-2';
import {primeClassroomAudio,disconnectClassroomAudio,classroomAudioOutputState} from './classroom-audio-output.js?v=native-pcm-20261017-1';
const $=id=>document.getElementById(id),query=new URLSearchParams(location.search);window.fRendererReady=true;
let course,manifest,prepared,board=0,audio=new Audio(),playing=false,language='zh',generation=0,requestedTime=0,courseEpoch=0,preparing=false,playIntent=false,completedWall=0;
if(query.has('testSilent'))audio.muted=true;
let finishCurrent=()=>{},openingLocked=false;
async function playPrepared(target=audio,mine=generation){await primeClassroomAudio(target);if(target!==audio||mine!==generation||!playIntent){if(target!==audio)disconnectClassroomAudio(target);return false;}target.playbackRate=classroomAudioRate(manifest?.boards[board],target.currentTime,1);await target.play();return true;}
const audioJobs=new Map(),audioURLs=new Set(),compressedJobs=new Map(),audioFiles=new Map();
function trimAudioURLs(){const keep=new Set([manifest?.boards[board]?.file,manifest?.boards[board+1]?.file]);for(const [file,url] of audioFiles)if(!keep.has(file)){URL.revokeObjectURL(url);audioURLs.delete(url);audioFiles.delete(file);audioJobs.delete(file);}}
async function compressedAudio(file){if(!compressedJobs.has(file)){const job=(async()=>{const r=await fetch(file);if(!r.ok)throw Error('本板语音下载失败');return r.blob();})().catch(e=>{if(compressedJobs.get(file)===job)compressedJobs.delete(file);throw e;});compressedJobs.set(file,job);}return compressedJobs.get(file);}
async function audioURL(file){if(!audioJobs.has(file)){const mine=courseEpoch,job=(async()=>{const blob=await compressedAudio(file),item=manifest?.boards.find(b=>b.file===file),pcm=await prepareClassroomAudioBlob(blob,{expectedSeconds:item?.seconds});if(mine!==courseEpoch)return null;const url=URL.createObjectURL(pcm);audioURLs.add(url);audioFiles.set(file,url);trimAudioURLs();return url;})().catch(e=>{if(audioJobs.get(file)===job)audioJobs.delete(file);throw e;});audioJobs.set(file,job);}return audioJobs.get(file);}
const fmt=s=>`${Math.floor(s/60)}:${String(Math.floor(s%60)).padStart(2,'0')}`;
const escape=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
function manuscript(b){
 const container=$('script');container.replaceChildren();
 const item=manifest?.boards[board],paragraphs=(manifest?.paragraphs||[]).filter(q=>q.page===board).sort((a,b)=>a.start-b.start);
 const note=document.createElement('p');note.textContent='按当前音频的实际播放顺序排列；板面行号与口播顺序分别标记。';container.append(note);
 const link=document.createElement('a');link.href='./assets/chalk/zzl-first-period-20261018/manuscript.md';link.textContent='查看与当前语音配套的完整讲稿';link.target='_blank';container.append(link);
 if(!item||!paragraphs.length){const status=document.createElement('p');status.textContent='当前音频时间轴尚未就绪。';container.append(status);return;}
 const clock=t=>`${String(Math.floor(t/60)).padStart(2,'0')}:${(t%60).toFixed(1).padStart(4,'0')}`;
 const entries=paragraphs.map((q,i)=>({kind:'speech',time:q.start-item.start,q,i})).concat((item.waits||[]).map(q=>({kind:'wait',time:q.start,q}))).sort((a,b)=>a.time-b.time);
 for(const event of entries){
  const q=event.q;
  if(event.kind==='wait'){const p=document.createElement('p');p.className='wait';p.textContent=`${clock(q.start)}–${clock(q.end)} · 思考${q.seconds}秒；结束后继续。`;container.append(p);continue;}
  const row=q.row==null?null:b.rows[q.row],el=document.createElement('article');
  el.dataset.line=q.lineId||'';el.dataset.start=String(q.start-item.start);el.dataset.end=String(q.end-item.start);
  const source=row?`板面第${q.row+1}行`:(q.role==='question'?'提问（不写板面）':'图示说明');
  const code=document.createElement('code');code.textContent=`口播${event.i+1} · ${clock(q.start-item.start)}–${clock(q.end-item.start)} · ${source}`;el.append(code);
  if(row){const display=document.createElement('p');display.textContent=language==='en'?(row.en||row.display):row.display;el.append(display);}
  const speech=document.createElement('p');speech.className='speech';speech.textContent='口播：'+q.text;el.append(speech);container.append(el);
 }
}

async function loadCourse(){const n=++courseEpoch;++generation;audio.pause();playing=false;playIntent=false;course=null;manifest=null;prepared=null;board=0;openingLocked=false;for(const url of audioURLs)URL.revokeObjectURL(url);audioURLs.clear();audioJobs.clear();compressedJobs.clear();audioFiles.clear();const id=$('course').value;
 const nextCourse=await fetch('./assets/chalk/zzl-first-period-20261018/course.json',{cache:'no-store'}).then(r=>r.json());if(n!==courseEpoch)return;course=nextCourse;
 const local=false,audioRoot='./assets/audio/courses/zzl-first-period-20261018/';
 const nextManifest=await fetch(audioRoot+(local?'口播与时间总表.json':'narration.json'),{cache:'no-store'}).then(r=>r.ok?r.json():null).catch(()=>null);if(n!==courseEpoch)return;manifest=nextManifest?selectClassroomOpening(nextManifest):null;
 if(manifest)for(const b of manifest.boards)b.file=audioRoot+(local?'逐板音频/':'')+b.file.split('/').pop();
 if(n!==courseEpoch)return;$('board-select').replaceChildren(...course.boards.map((b,i)=>{const o=document.createElement('option');o.value=i;o.textContent=`${i+1} · ${b.title}`;return o}));
 $('assistant').textContent=course.assistantPlan.map(x=>`${x.minutes}分钟 · ${x.topic}：${x.task}`).join('\n');$('assistant').style.whiteSpace='pre-line';
 $('duration').textContent=manifest?`仅第一课时 · ${fmt(manifest.duration)} · 播放100% · 成品口播放慢10% · 提问音量提高10% · 简单练习30秒 / 挑战练习60秒。清晰度与热情度待你试听确认。`:'语音尚未准备好，可先查看讲稿。';
 $('play').disabled=!manifest;$('seek').disabled=!manifest;
 await selectBoard(Math.min(Number(query.get('board')||0),course.boards.length-1),false);
 // First board ready: preload all later board MP3s in a bounded queue.
 if(manifest){const queue=manifest.boards.slice(board+1,board+3).filter(b=>b.file);let cursor=0;void Promise.all(Array.from({length:1},async()=>{while(cursor<queue.length&&n===courseEpoch){const b=queue[cursor++];try{await compressedAudio(b.file);}catch{}}}));}
}
async function selectBoard(index,resume=playIntent){const n=++generation;playIntent=resume;preparing=true;$('complete').disabled=true;playing=false;audio.pause();completedWall=0;prepared=null;audio.currentTime=0;const blank=$('board').getContext('2d');blank.fillStyle='#06271c';blank.fillRect(0,0,1536,640);board=Math.max(0,Math.min(course.boards.length-1,index));$('board-select').value=board;$('status').textContent='正在准备本板字迹与整块语音…';const b=course.boards[board];manuscript(b);
 const nextPrepared=b.kind==='break'?null:await prepareBoard(b,language);if(n!==generation)return;prepared=nextPrepared;if(prepared)prepared.total=course.boards.length;
 const item=manifest?.boards[board];audio.onended=null;audio.onplay=null;audio.onpause=null;audio.preload='auto';audio.preservesPitch=true;audio.playbackRate=classroomAudioRate(item,0,1);requestedTime=0;
 if(item?.file){const src=await audioURL(item.file);if(n!==generation)return;audio.src=src;await new Promise((resolve,reject)=>{audio.addEventListener('loadedmetadata',resolve,{once:true});audio.addEventListener('error',()=>reject(Error('本板语音加载失败，可重试或换板')),{once:true});audio.load();});trimAudioURLs();const next=manifest.boards[board+1];if(next?.file)void audioURL(next.file).catch(()=>{});}
 if(n!==generation)return;preparing=false;$('complete').disabled=false;const target=audio,valid=()=>n===generation&&audio===target;finishCurrent=()=>{if(!valid()||!playIntent)return;const remaining=completedWall?MIN_BOARD_REVIEW_SECONDS-(Date.now()-completedWall)/1000:0;if(remaining>0){setTimeout(finishCurrent,Math.min(1000,remaining*1000));return;}if(board<course.boards.length-1)selectBoard(board+1,true);else{playing=false;playIntent=false;update();}};audio.onended=finishCurrent;audio.onplay=()=>{if(valid()){playing=true;update()}};audio.onpause=()=>{if(valid()){playing=false;update()}};paint();if(playIntent&&item?.file)await playPrepared(audio,n);update();
}
function update(){$('play').textContent=playIntent?'暂停':'播放';$('status').textContent=`${course?.title||''} · ${board+1} / ${course?.boards.length||0} · ZZL / F${!manifest?' · 文本与板书预览':''}`;}
let countdownHit=null;
function skipCountdown(){const item=manifest?.boards[board],wait=boardWaitAt(item,audio.currentTime);if(preparing||!wait)return false;audio.currentTime=wait.end+.001;paint();return true;}
function paint(){countdownHit=null;if(!course)return;const b=course.boards[board],item=manifest?.boards[board],t=item?audio.currentTime:requestedTime,cx=$('board').getContext('2d');
 if(item){const rate=classroomAudioRate(item,t,1);if(audio.playbackRate!==rate)audio.playbackRate=rate;}
 if(b.kind==='break'){cx.fillStyle='#06271c';cx.fillRect(0,0,1536,640);cx.fillStyle='#e4cf9c';cx.font='92px RefugeChinese';cx.textAlign='center';cx.fillText('课间休息',768,250);cx.font='88px sans-serif';cx.fillText(fmt(Math.min(300,Math.max(0,(item?.seconds||300)-t))),768,405);cx.textAlign='left';return;}
 if(!prepared)return;const fractions={};if(item){for(const w of item.writing)fractions[w.logical]=Math.max(fractions[w.logical]||0,Math.min(1,Math.max(0,(t-w.start)/(w.end-w.start))));}else Object.keys(prepared.logical).forEach(k=>fractions[k]=1);
 paintPrepared(cx,prepared,fractions);if(item&&t>=item.lastStrokeEnd){completedWall ||= Date.now();}else completedWall=0;const wait=item?.waits?.find(w=>t>=w.start&&t<w.end);if(wait){cx.fillStyle='#e4cf9c';cx.font='72px sans-serif';cx.textAlign='center';const text=fmt(Math.ceil(wait.end-t)),y=b.kind==='exercise'?425:575;cx.fillText(text,768,y);countdownHit=countdownTextRect(cx,text,768,y,78);cx.textAlign='left';}
 for(const e of $('script').querySelectorAll('article'))e.classList.toggle('active',t>=Number(e.dataset.start)&&t<Number(e.dataset.end));
 if(item)$('seek').value=audio.currentTime/item.seconds*1000;
}
$('course').onchange=()=>loadCourse().catch(e=>$('status').textContent=e.message);$('board-select').onchange=e=>selectBoard(+e.target.value).catch(e=>$('status').textContent=e.message);
$('prev').onclick=()=>selectBoard(board-1).catch(e=>$('status').textContent=e.message);$('next').onclick=()=>selectBoard(board+1).catch(e=>$('status').textContent=e.message);
$('play').onclick=async()=>{if(!openingLocked&&board===0&&manifest?.openingSelection&&manifest.openingSelection.period!==openingPeriod())await loadCourse();openingLocked=true;if(!manifest){$('status').textContent='本板音频尚在生成，请先审阅逐行稿。';return;}playIntent=!playIntent;if(preparing){update();return;}if(!playIntent){audio.pause();}else{const b=manifest.boards[board];if(audio.ended||audio.currentTime>=b.seconds-.02){finishCurrent();update();return;}if(completedWall&&b.boardHoldSeconds>0&&audio.currentTime>=b.seconds-b.boardHoldSeconds)audio.currentTime=Math.min(b.seconds-.005,Math.max(audio.currentTime,b.lastStrokeEnd+(Date.now()-completedWall)/1000));await playPrepared();}update();};
$('complete').onclick=()=>{playIntent=false;audio.pause();playing=false;if(manifest)audio.currentTime=Math.max(0,manifest.boards[board].seconds-.01);requestedTime=Infinity;completedWall=Date.now();paint();update();};
$('lang').onclick=async()=>{const resume=playIntent,t=audio.currentTime;language=language==='zh'?'en':'zh';await selectBoard(board,resume);if(manifest)audio.currentTime=t;paint();};
$('seek').oninput=()=>{if(manifest){audio.currentTime=Number($('seek').value)/1000*manifest.boards[board].seconds;completedWall=audio.currentTime>=manifest.boards[board].lastStrokeEnd?Date.now():0;}paint();};
const countdownPoint=e=>{const r=$('board').getBoundingClientRect();return [(e.clientX-r.left)*1536/r.width,(e.clientY-r.top)*640/r.height];};
$('board').addEventListener('click',e=>{if(containsCountdown(countdownHit,...countdownPoint(e)))skipCountdown();});
$('board').addEventListener('pointermove',e=>{const hit=containsCountdown(countdownHit,...countdownPoint(e));$('board').style.cursor=hit?'pointer':'';$('board').title=hit?'点击跳过剩余思考':'';});
function frame(){paint();if(!countdownHit){$('board').style.cursor='';$('board').title='';}requestAnimationFrame(frame)}requestAnimationFrame(frame);
if(query.get('course'))$('course').value=query.get('course');
if(!query.has('measure'))loadCourse().catch(e=>{$('status').textContent=e.message;console.error(e)});
window.fClassroom={selectBoard,loadCourse,skipCountdown,getState:()=>({countdownHit,board,playing,language,prepared,manifest,course,audio,output:classroomAudioOutputState(),decode:classroomAudioDecodeState(),audioCache:{compressed:compressedJobs.size,decoded:audioFiles.size}}),setTime:t=>{audio.pause();audio.currentTime=t;paint();}};
const focusPause=()=>{playIntent=false;audio.pause();};addEventListener('blur',focusPause);document.addEventListener('visibilitychange',()=>{if(document.hidden)focusPause();});
