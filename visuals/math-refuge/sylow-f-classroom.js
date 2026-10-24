import {renderClassroomManuscript} from './classroom-manuscript.js?v=C-full-20261019';

import {CLASSROOM_PROGRAMS,classroomProgram} from './classroom-catalog.js?v=zl-name-20261024';

import {createCoursePreload} from './course-preload.js?v=rings-20261022';

import {boardWaitAt,countdownTextRect,containsCountdown} from './board-countdown.js';

import {MIN_BOARD_REVIEW_SECONDS,boardReviewStart} from './board-review.js?v=uniform-review-20261019';

import {prepareClassroomAudioBlob,classroomAudioDecodeState} from './classroom-audio-decode.js?v=mp3-predecode-1';

import {prepareBoard,paintPrepared} from './sylow-f-renderer.js?v=rings-20261022';

import {selectClassroomOpening,openingPeriod,classroomAudioRate,classroomDuration} from './classroom-opening.js?v=uniform-review-20261019';

import {primeClassroomAudio,disconnectClassroomAudio,classroomAudioOutputState} from './classroom-audio-output.js?v=native-pcm-20261017-1';

import {createClassroomBeachBreak} from './classroom-beach-break.js?v=break-cloud20-20261024';

const $=id=>document.getElementById(id),query=new URLSearchParams(location.search);window.fRendererReady=true;

let course,manifest,prepared,board=0,audio=new Audio(),playing=false,language='zh',generation=0,requestedTime=0,courseEpoch=0,preparing=false,playIntent=false,completedWall=0;

if(query.has('testSilent'))audio.muted=true;

const lessonRate=()=>manifest?.policy?.defaultPlaybackRate||1;

let finishCurrent=()=>{},openingLocked=false;

const beachBreak=createClassroomBeachBreak({

 onState:s=>{if(course?.boards[board]?.kind==='break'){playIntent=s.resumeLecture;playing=s.playing&&s.ready;update();}},

 onFinish:s=>{if(course?.boards[board]?.kind==='break'&&s.key===course.id+':'+board+':'+generation)return selectBoard(board+1,s.resume);},

 onError:error=>{$('status').textContent=error;}

});

async function playPrepared(target=audio,mine=generation){await primeClassroomAudio(target);if(target!==audio||mine!==generation||!playIntent){if(target!==audio)disconnectClassroomAudio(target);return false;}target.playbackRate=classroomAudioRate(manifest?.boards[board],target.currentTime,lessonRate());await target.play();return true;}

const audioJobs=new Map(),audioURLs=new Set(),compressedJobs=new Map(),audioFiles=new Map();

const assetPreload=createCoursePreload({concurrency:2});

function trimAudioURLs(){const keep=new Set([manifest?.boards[board]?.file,manifest?.boards[board+1]?.file]);for(const [file,url] of audioFiles)if(!keep.has(file)){URL.revokeObjectURL(url);audioURLs.delete(url);audioFiles.delete(file);audioJobs.delete(file);}}

async function compressedAudio(file){if(!compressedJobs.has(file)){const job=(async()=>{const r=await fetch(file);if(!r.ok)throw Error('本板语音下载失败');return r.blob();})().catch(e=>{if(compressedJobs.get(file)===job)compressedJobs.delete(file);throw e;});compressedJobs.set(file,job);}return compressedJobs.get(file);}

async function audioURL(file){if(!audioJobs.has(file)){const mine=courseEpoch,job=(async()=>{const blob=await compressedAudio(file),item=manifest?.boards.find(b=>b.file===file),pcm=await prepareClassroomAudioBlob(blob,{expectedSeconds:item?.seconds});if(mine!==courseEpoch)return null;const url=URL.createObjectURL(pcm);audioURLs.add(url);audioFiles.set(file,url);trimAudioURLs();return url;})().catch(e=>{if(audioJobs.get(file)===job)audioJobs.delete(file);throw e;});audioJobs.set(file,job);}return audioJobs.get(file);}

const fmt=s=>`${Math.floor(s/60)}:${String(Math.floor(s%60)).padStart(2,'0')}`;

const escape=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));

function manuscript(b){renderClassroomManuscript($('script'),b,manifest,board);}

function assistantPlanText(plan){

 const entries=Array.isArray(plan)?plan:plan&&typeof plan==='object'?[plan]:[];

 return entries.flatMap(item=>{

  if(!item||typeof item!=='object')return [];

  const minutes=Number.isFinite(item.minutes)?`${item.minutes}分钟`:'';

  const task=Array.isArray(item.tasks)?item.tasks.filter(x=>typeof x==='string').join('；'):[item.topic,item.task].filter(Boolean).join('：');

  return [[minutes,task].filter(Boolean).join(' · '),typeof item.note==='string'?item.note:''].filter(Boolean);

 }).join('\n');

}

async function loadCourse(){beachBreak.cancel();const n=++courseEpoch;++generation;audio.pause();assetPreload.cancel();playing=false;playIntent=false;course=null;manifest=null;prepared=null;board=0;openingLocked=false;for(const url of audioURLs)URL.revokeObjectURL(url);audioURLs.clear();audioJobs.clear();compressedJobs.clear();audioFiles.clear();const id=$('course').value;

 const program=classroomProgram(id);if(!program)throw Error('未找到这门板书课堂');

 const nextCourse=await fetch(program.courseManifest,{cache:'no-store'}).then(r=>{if(!r.ok)throw Error('本课板书下载失败');return r.json();});if(n!==courseEpoch)return;course=nextCourse;

 for(const b of course.boards)b.sectionLabel ||= b.section?'§'+String(b.section).replace(/^§/,''):'§'+program.section;

 document.title=program.topic+' · ZL课堂';

 const audioRoot=program.audioRoot;

 const nextManifest=await fetch(program.narration.manifest,{cache:'no-store'}).then(r=>r.ok?r.json():null).catch(()=>null);if(n!==courseEpoch)return;manifest=nextManifest?selectClassroomOpening(nextManifest):null;

 if(manifest)for(const b of manifest.boards)b.file=audioRoot+b.file.split('/').pop();

 if(manifest?.openingSelection){const r=course.boards[0].rows[1];r.speech=manifest.openingSelection.greeting+r.speech;}

 if(n!==courseEpoch)return;$('board-select').replaceChildren(...course.boards.map((b,i)=>{const o=document.createElement('option');o.value=i;o.textContent=`${i+1} · ${b.title}`;return o}));

 $('assistant').textContent=assistantPlanText(course.assistantPlan);$('assistant').style.whiteSpace='pre-line';

 $('duration').textContent=manifest?`C原版表达 · 播放100% · 本课约 ${fmt(classroomDuration(manifest,lessonRate()))}（含课间05:00）；简单练习30秒 / 有点挑战60秒；孟晟助教另计30:00。`:'本板语音尚未就绪，可重试或查看讲稿。';

 $('play').disabled=!manifest;$('seek').disabled=!manifest;

 await selectBoard(Math.min(Number(query.get('board')||0),course.boards.length-1),false);

 void assetPreload.start(course.boards.map(orderedBoard=>({orderedBoard})),{courseText:course.boards.flatMap(b=>b.rows.map(r=>r.display+' '+r.en)).join('\n')});

 // First board ready: preload all later board MP3s in a bounded queue.

 if(manifest){const queue=manifest.boards.slice(board+1).filter(b=>b.file&&!b.id.endsWith('-break'));let cursor=0;void Promise.all(Array.from({length:3},async()=>{while(cursor<queue.length&&n===courseEpoch){const b=queue[cursor++];try{await compressedAudio(b.file);}catch{}}}));}

}

async function selectBoard(index,resume=playIntent){const departureImage=course?.boards[Math.max(0,Math.min(course.boards.length-1,index))]?.kind==='break'?$('board').toDataURL('image/png'):null;beachBreak.cancel();const n=++generation;playIntent=resume;preparing=true;$('complete').disabled=true;playing=false;audio.pause();completedWall=0;prepared=null;audio.currentTime=0;const blank=$('board').getContext('2d');blank.fillStyle='#06271c';blank.fillRect(0,0,1536,640);board=Math.max(0,Math.min(course.boards.length-1,index));$('board-select').value=board;$('status').textContent='正在准备本板字迹与整块语音…';const b=course.boards[board];manuscript(b);

 if(b.kind==='break'){audio.onended=null;audio.onplay=null;audio.onpause=null;preparing=false;$('complete').disabled=false;requestedTime=0;await beachBreak.start({key:course.id+':'+board+':'+n,duration:300,playing:true,resumeLecture:resume,boardImage:departureImage});paint();update();return;}

 const nextPrepared=b.kind==='break'?null:await prepareBoard(b,language);if(n!==generation)return;prepared=nextPrepared;if(prepared)prepared.total=course.boards.length;

 const item=manifest?.boards[board];audio.onended=null;audio.onplay=null;audio.onpause=null;audio.preload='auto';audio.preservesPitch=true;audio.playbackRate=classroomAudioRate(item,0,lessonRate());requestedTime=0;

 if(item?.file){const src=await audioURL(item.file);if(n!==generation)return;audio.src=src;await new Promise((resolve,reject)=>{audio.addEventListener('loadedmetadata',resolve,{once:true});audio.addEventListener('error',()=>reject(Error('本板语音加载失败，可重试或换板')),{once:true});audio.load();});trimAudioURLs();const next=manifest.boards[board+1];if(next?.file)void audioURL(next.file).catch(()=>{});}

 if(n!==generation)return;preparing=false;$('complete').disabled=false;const target=audio,valid=()=>n===generation&&audio===target;finishCurrent=()=>{if(!valid()||!playIntent)return;paint();completedWall ||= Date.now();const remaining=b.kind==='break'?0:MIN_BOARD_REVIEW_SECONDS-(Date.now()-completedWall)/1000;if(remaining>0){setTimeout(finishCurrent,Math.min(1000,remaining*1000));return;}if(board<course.boards.length-1)selectBoard(board+1,true);else{playing=false;playIntent=false;update();}};audio.onended=finishCurrent;audio.onplay=()=>{if(valid()){playing=true;update()}};audio.onpause=()=>{if(valid()){playing=false;update()}};paint();if(playIntent&&item?.file)await playPrepared(audio,n);update();

}

function update(){$('play').textContent=playIntent?'暂停':'播放';$('status').textContent=`${course?.title||''} · ${board+1} / ${course?.boards.length||0} · ZL / C${!manifest?' · 文本与板书预览':''}`;}

let countdownHit=null;

function skipCountdown(){const item=manifest?.boards[board],wait=boardWaitAt(item,audio.currentTime);if(preparing||!wait)return false;audio.currentTime=wait.end+.001;paint();return true;}

function paint(){countdownHit=null;if(!course)return;const b=course.boards[board],item=manifest?.boards[board],t=beachBreak.state?.elapsed??(item?audio.currentTime:requestedTime),cx=$('board').getContext('2d');

 if(item){const rate=classroomAudioRate(item,t,lessonRate());if(audio.playbackRate!==rate)audio.playbackRate=rate;}

 if(b.kind==='break'){cx.fillStyle='#06271c';cx.fillRect(0,0,1536,640);cx.fillStyle='#e4cf9c';cx.font='92px RefugeChinese';cx.textAlign='center';cx.fillText('课间休息',768,250);cx.font='88px sans-serif';cx.fillText(fmt(Math.min(300,Math.max(0,(item?.seconds||300)-t))),768,405);cx.textAlign='left';return;}

 if(!prepared)return;const fractions={};if(item){for(const w of item.writing)fractions[w.logical]=Math.max(fractions[w.logical]||0,Math.min(1,Math.max(0,(t-w.start)/(w.end-w.start))));}else Object.keys(prepared.logical).forEach(k=>fractions[k]=1);

 paintPrepared(cx,prepared,fractions);if(item&&t>=boardReviewStart(item)){completedWall ||= Date.now();}else completedWall=0;const wait=item?.waits?.find(w=>t>=w.start&&t<w.end);if(wait){cx.fillStyle='#e4cf9c';cx.font='72px sans-serif';cx.textAlign='center';const text=fmt(Math.ceil(wait.end-t)),y=b.kind==='exercise'?425:575;cx.fillText(text,768,y);countdownHit=countdownTextRect(cx,text,768,y,78);cx.textAlign='left';}

 for(const e of $('script').querySelectorAll('article'))e.classList.toggle('active',t>=Number(e.dataset.start)&&t<Number(e.dataset.end));

 if(item)$('seek').value=audio.currentTime/item.seconds*1000;

}

$('course').onchange=()=>loadCourse().catch(e=>$('status').textContent=e.message);$('board-select').onchange=e=>selectBoard(+e.target.value).catch(e=>$('status').textContent=e.message);

$('prev').onclick=()=>selectBoard(board-1).catch(e=>$('status').textContent=e.message);$('next').onclick=()=>selectBoard(board+1).catch(e=>$('status').textContent=e.message);

$('play').onclick=async()=>{if(beachBreak.state){if(beachBreak.state.playing)beachBreak.pause();else beachBreak.play();return;}if(!openingLocked&&board===0&&manifest?.openingSelection&&manifest.openingSelection.period!==openingPeriod())await loadCourse();openingLocked=true;if(!manifest){$('status').textContent='本板音频尚在生成，请先审阅逐行稿。';return;}playIntent=!playIntent;if(preparing){update();return;}if(!playIntent){audio.pause();}else{const b=manifest.boards[board];if(audio.ended||audio.currentTime>=b.seconds-.02){finishCurrent();update();return;}if(completedWall&&b.boardHoldSeconds>0&&audio.currentTime>=b.seconds-b.boardHoldSeconds)audio.currentTime=Math.min(b.seconds-.005,Math.max(audio.currentTime,boardReviewStart(b)+(Date.now()-completedWall)/1000));await playPrepared();}update();};

$('complete').onclick=()=>{if(beachBreak.state){beachBreak.pause();beachBreak.seek(300);paint();return;}playIntent=false;audio.pause();playing=false;if(manifest)audio.currentTime=Math.max(0,manifest.boards[board].seconds-.01);requestedTime=Infinity;completedWall=Date.now();paint();update();};

$('lang').onclick=async()=>{const resume=playIntent,t=audio.currentTime;language=language==='zh'?'en':'zh';await selectBoard(board,resume);if(manifest)audio.currentTime=t;paint();};

$('seek').oninput=()=>{if(beachBreak.state){beachBreak.seek(Number($('seek').value)/1000*300);paint();return;}if(manifest){audio.currentTime=Number($('seek').value)/1000*manifest.boards[board].seconds;completedWall=audio.currentTime>=boardReviewStart(manifest.boards[board])?Date.now():0;}paint();};

const countdownPoint=e=>{const r=$('board').getBoundingClientRect();return [(e.clientX-r.left)*1536/r.width,(e.clientY-r.top)*640/r.height];};

$('board').addEventListener('click',e=>{if(containsCountdown(countdownHit,...countdownPoint(e)))skipCountdown();});

$('board').addEventListener('pointermove',e=>{const hit=containsCountdown(countdownHit,...countdownPoint(e));$('board').style.cursor=hit?'pointer':'';$('board').title=hit?'点击跳过剩余思考':'';});

function frame(){paint();if(!countdownHit){$('board').style.cursor='';$('board').title='';}requestAnimationFrame(frame)}requestAnimationFrame(frame);

$('course').replaceChildren(...CLASSROOM_PROGRAMS.map(program=>{const option=document.createElement('option');option.value=program.id;option.textContent=program.topic.replace(/^§/,'');return option;}));

if(classroomProgram(query.get('course')))$('course').value=query.get('course');

if(!query.has('measure'))loadCourse().catch(e=>{$('status').textContent=e.message;console.error(e)});

window.fClassroom={selectBoard,loadCourse,skipCountdown,getState:()=>({countdownHit,board,playing,language,prepared,manifest,course,audio,beachBreak:beachBreak.state,output:classroomAudioOutputState(),decode:classroomAudioDecodeState(),assetPreload:assetPreload.state,audioCache:{compressed:compressedJobs.size,decoded:audioFiles.size}}),setTime:t=>{if(beachBreak.state){beachBreak.seek(t);paint();return;}audio.pause();audio.currentTime=t;paint();}};

const focusPause=()=>{if(beachBreak.state)return;playIntent=false;audio.pause();};addEventListener('blur',focusPause);document.addEventListener('visibilitychange',()=>{if(document.hidden)focusPause();});

