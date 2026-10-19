import {renderClassroomManuscript} from './classroom-manuscript.js?v=C-full-20261019';
import {boardWaitAt,countdownTextRect,containsCountdown} from './board-countdown.js';
import {MIN_BOARD_REVIEW_SECONDS} from './board-review.js';
import {prepareClassroomAudioBlob,classroomAudioDecodeState} from './classroom-audio-decode.js?v=mp3-predecode-1';
import {prepareBoard,paintPrepared} from './sylow-f-renderer.js?v=C-full-20261019';
import {selectClassroomOpening,openingPeriod,classroomAudioRate,classroomDuration} from './classroom-opening.js?v=exercise-C-20261018';
import {primeClassroomAudio,disconnectClassroomAudio,classroomAudioOutputState} from './classroom-audio-output.js?v=native-pcm-20261017-1';
const $=id=>document.getElementById(id),query=new URLSearchParams(location.search);window.fRendererReady=true;
let course,manifest,prepared,board=0,audio=new Audio(),playing=false,language='zh',generation=0,requestedTime=0,courseEpoch=0,preparing=false,playIntent=false,completedWall=0;
if(query.has('testSilent'))audio.muted=true;
const lessonRate=()=>manifest?.policy?.defaultPlaybackRate||1;
let finishCurrent=()=>{},openingLocked=false;
async function playPrepared(target=audio,mine=generation){await primeClassroomAudio(target);if(target!==audio||mine!==generation||!playIntent){if(target!==audio)disconnectClassroomAudio(target);return false;}target.playbackRate=classroomAudioRate(manifest?.boards[board],target.currentTime,lessonRate());await target.play();return true;}
const audioJobs=new Map(),audioURLs=new Set(),compressedJobs=new Map(),audioFiles=new Map();
function trimAudioURLs(){const keep=new Set([manifest?.boards[board]?.file,manifest?.boards[board+1]?.file]);for(const [file,url] of audioFiles)if(!keep.has(file)){URL.revokeObjectURL(url);audioURLs.delete(url);audioFiles.delete(file);audioJobs.delete(file);}}
async function compressedAudio(file){if(!compressedJobs.has(file)){const job=(async()=>{const r=await fetch(file);if(!r.ok)throw Error('本板语音下载失败');return r.blob();})().catch(e=>{if(compressedJobs.get(file)===job)compressedJobs.delete(file);throw e;});compressedJobs.set(file,job);}return compressedJobs.get(file);}
async function audioURL(file){if(!audioJobs.has(file)){const mine=courseEpoch,job=(async()=>{const blob=await compressedAudio(file),item=manifest?.boards.find(b=>b.file===file),pcm=await prepareClassroomAudioBlob(blob,{expectedSeconds:item?.seconds});if(mine!==courseEpoch)return null;const url=URL.createObjectURL(pcm);audioURLs.add(url);audioFiles.set(file,url);trimAudioURLs();return url;})().catch(e=>{if(audioJobs.get(file)===job)audioJobs.delete(file);throw e;});audioJobs.set(file,job);}return audioJobs.get(file);}
const fmt=s=>`${Math.floor(s/60)}:${String(Math.floor(s%60)).padStart(2,'0')}`;
const escape=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
function manuscript(b){renderClassroomManuscript($('script'),b,manifest,board);}
async function loadCourse(){const n=++courseEpoch;++generation;audio.pause();playing=false;playIntent=false;course=null;manifest=null;prepared=null;board=0;openingLocked=false;for(const url of audioURLs)URL.revokeObjectURL(url);audioURLs.clear();audioJobs.clear();compressedJobs.clear();audioFiles.clear();const id=$('course').value;
 const nextCourse=await fetch('./assets/chalk/zzl-c-20261019/'+id+(id==='sylow-theorems'?'-abelian-v1.json':'.json'),{cache:'no-store'}).then(r=>r.json());if(n!==courseEpoch)return;course=nextCourse;
 const audioRoot='./assets/audio/courses/zzl-c-20261019/'+id+'/';
 const nextManifest=await fetch(audioRoot+(id==='sylow-theorems'?'narration-abelian-v1.json':'narration.json'),{cache:'no-store'}).then(r=>r.ok?r.json():null).catch(()=>null);if(n!==courseEpoch)return;manifest=nextManifest?selectClassroomOpening(nextManifest):null;
 if(manifest)for(const b of manifest.boards)b.file=audioRoot+b.file.split('/').pop();
 if(manifest?.openingSelection){const r=course.boards[0].rows[1];r.speech=manifest.openingSelection.greeting+r.speech;}
 if(n!==courseEpoch)return;$('board-select').replaceChildren(...course.boards.map((b,i)=>{const o=document.createElement('option');o.value=i;o.textContent=`${i+1} · ${b.title}`;return o}));
 $('assistant').textContent=course.assistantPlan.map(x=>`${x.minutes}分钟 · ${x.topic}：${x.task}`).join('\n');$('assistant').style.whiteSpace='pre-line';
 $('duration').textContent=manifest?`C原版表达 · 播放100% · 本课约 ${fmt(classroomDuration(manifest,lessonRate()))}（含课间05:00）；简单练习30秒 / 有点挑战60秒；孟晟助教另计30:00。`:'本板语音尚未就绪，可重试或查看讲稿。';
 $('play').disabled=!manifest;$('seek').disabled=!manifest;
 await selectBoard(Math.min(Number(query.get('board')||0),course.boards.length-1),false);
 // First board ready: preload all later board MP3s in a bounded queue.
 if(manifest){const queue=manifest.boards.slice(board+1).filter(b=>b.file&&!b.id.endsWith('-break'));let cursor=0;void Promise.all(Array.from({length:3},async()=>{while(cursor<queue.length&&n===courseEpoch){const b=queue[cursor++];try{await compressedAudio(b.file);}catch{}}}));}
}
async function selectBoard(index,resume=playIntent){const n=++generation;playIntent=resume;preparing=true;$('complete').disabled=true;playing=false;audio.pause();completedWall=0;prepared=null;audio.currentTime=0;const blank=$('board').getContext('2d');blank.fillStyle='#06271c';blank.fillRect(0,0,1536,640);board=Math.max(0,Math.min(course.boards.length-1,index));$('board-select').value=board;$('status').textContent='正在准备本板字迹与整块语音…';const b=course.boards[board];manuscript(b);
 const nextPrepared=b.kind==='break'?null:await prepareBoard(b,language);if(n!==generation)return;prepared=nextPrepared;if(prepared)prepared.total=course.boards.length;
 const item=manifest?.boards[board];audio.onended=null;audio.onplay=null;audio.onpause=null;audio.preload='auto';audio.preservesPitch=true;audio.playbackRate=classroomAudioRate(item,0,lessonRate());requestedTime=0;
 if(item?.file){const src=await audioURL(item.file);if(n!==generation)return;audio.src=src;await new Promise((resolve,reject)=>{audio.addEventListener('loadedmetadata',resolve,{once:true});audio.addEventListener('error',()=>reject(Error('本板语音加载失败，可重试或换板')),{once:true});audio.load();});trimAudioURLs();const next=manifest.boards[board+1];if(next?.file)void audioURL(next.file).catch(()=>{});}
 if(n!==generation)return;preparing=false;$('complete').disabled=false;const target=audio,valid=()=>n===generation&&audio===target;finishCurrent=()=>{if(!valid()||!playIntent)return;const remaining=completedWall?MIN_BOARD_REVIEW_SECONDS-(Date.now()-completedWall)/1000:0;if(remaining>0){setTimeout(finishCurrent,Math.min(1000,remaining*1000));return;}if(board<course.boards.length-1)selectBoard(board+1,true);else{playing=false;playIntent=false;update();}};audio.onended=finishCurrent;audio.onplay=()=>{if(valid()){playing=true;update()}};audio.onpause=()=>{if(valid()){playing=false;update()}};paint();if(playIntent&&item?.file)await playPrepared(audio,n);update();
}
function update(){$('play').textContent=playIntent?'暂停':'播放';$('status').textContent=`${course?.title||''} · ${board+1} / ${course?.boards.length||0} · ZZL / C${!manifest?' · 文本与板书预览':''}`;}
let countdownHit=null;
function skipCountdown(){const item=manifest?.boards[board],wait=boardWaitAt(item,audio.currentTime);if(preparing||!wait)return false;audio.currentTime=wait.end+.001;paint();return true;}
function paint(){countdownHit=null;if(!course)return;const b=course.boards[board],item=manifest?.boards[board],t=item?audio.currentTime:requestedTime,cx=$('board').getContext('2d');
 if(item){const rate=classroomAudioRate(item,t,lessonRate());if(audio.playbackRate!==rate)audio.playbackRate=rate;}
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
