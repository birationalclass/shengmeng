import {prepareBoard,paintPrepared} from './sylow-f-renderer.js';
import {selectClassroomOpening,openingPeriod,classroomAudioRate,classroomDuration} from './classroom-opening.js?v=classroom-clarity-20261017-2';
import {primeClassroomAudio,disconnectClassroomAudio,classroomAudioOutputState} from './classroom-audio-output.js?v=pcm-wav-20261017-1';
const $=id=>document.getElementById(id),query=new URLSearchParams(location.search);window.fRendererReady=true;
let course,manifest,prepared,board=0,audio=new Audio(),playing=false,language='zh',generation=0,requestedTime=0,courseEpoch=0,preparing=false,playIntent=false,completedWall=0;
let finishCurrent=()=>{},openingLocked=false;
async function playPrepared(target=audio,mine=generation){await primeClassroomAudio(target);if(target!==audio||mine!==generation||!playIntent){if(target!==audio)disconnectClassroomAudio(target);return false;}await target.play();return true;}
const audioJobs=new Map(),audioURLs=new Set();
async function audioURL(file){if(!audioJobs.has(file))audioJobs.set(file,(async()=>{const r=await fetch(file);if(!r.ok)throw Error('本板语音下载失败');const blob=await r.blob(),url=URL.createObjectURL(blob);audioURLs.add(url);return url;})().catch(e=>{audioJobs.delete(file);throw e;}));return audioJobs.get(file);}
const fmt=s=>`${Math.floor(s/60)}:${String(Math.floor(s%60)).padStart(2,'0')}`;
const escape=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
function manuscript(b){$('script').replaceChildren();for(const r of b.rows){const el=document.createElement('article');el.dataset.line=r.id;el.innerHTML=`<code>${escape(r.id)}</code><p>${escape(r.display)}</p><p class="speech">口播：${escape(r.speech||'封面课程标记')}</p>`;$('script').append(el);const i=b.rows.indexOf(r);if(b.question?.afterRow===i){const p=document.createElement('p');p.className='wait';p.textContent='旁白提问：'+b.question.text+' → 思考10秒，再继续。';$('script').append(p);}if(b.kind==='exercise'&&b.thinkingAfterRow===i){const p=document.createElement('p');p.className='wait';p.textContent='独立思考60秒；答案及讲评在倒计时结束后呈现。';$('script').append(p);}if(b.diagram&&b.diagramAfterRow===i){const p=document.createElement('p');p.className='diagram-link';p.innerHTML=`<a href="${b.diagramAsset}" target="_blank">图例 ${b.id}.V01 · 数据文件</a><br>${b.diagramSpeech.map((s,j)=>`阶段${j+1}口播：${escape(s)}`).join('<br>')}`;$('script').append(p);}}}
async function loadCourse(){const n=++courseEpoch;++generation;audio.pause();playing=false;playIntent=false;course=null;manifest=null;prepared=null;board=0;openingLocked=false;for(const url of audioURLs)URL.revokeObjectURL(url);audioURLs.clear();audioJobs.clear();const id=$('course').value;
 const nextCourse=await fetch('./assets/chalk/zzl-f/'+id+'.json',{cache:'no-store'}).then(r=>r.json());if(n!==courseEpoch)return;course=nextCourse;
 const privateRoot='/02_报告与语音/数学难民营讲稿/声音建模/ZZL/12_代数学I_2.6上下_F逐行课堂/';
 const nextManifest=query.get('local')==='1'?await fetch(privateRoot+id+'/口播与时间总表.json',{cache:'no-store'}).then(r=>r.ok?r.json():null).catch(()=>null):null;if(n!==courseEpoch)return;manifest=nextManifest?selectClassroomOpening(nextManifest):null;
 if(manifest)for(const b of manifest.boards)b.file=privateRoot+id+'/逐板音频/'+b.file.split('/').pop();
 if(manifest?.openingSelection){const r=course.boards[0].rows[1];r.speech=manifest.openingSelection.greeting+r.speech;}
 if(n!==courseEpoch)return;$('board-select').replaceChildren(...course.boards.map((b,i)=>{const o=document.createElement('option');o.value=i;o.textContent=`${i+1} · ${b.title}`;return o}));
 $('assistant').textContent=course.assistantPlan.map(x=>`${x.minutes}分钟 · ${x.topic}：${x.task}`).join('\n');$('assistant').style.whiteSpace='pre-line';
 $('duration').textContent=manifest?`主讲 ${fmt(manifest.durationWithoutBreak)}；课间 ${fmt(300)}；合计 ${fmt(manifest.duration)}；孟晟助教另计30:00。`:'ZZL/F口播仅本机保存；本页提供板书与逐行讲稿审阅。';
 if(!manifest&&course.timingSummary)$('duration').textContent=`本机成品排程：主讲 ${fmt(course.timingSummary.durationWithoutBreak)} + 课间5:00；合计 ${fmt(course.timingSummary.duration)}。孟晟助教另计30:00。ZZL/F音频仅本机保存。`;
 if(!manifest&&course.timingSummary?.playbackTiming)$('duration').textContent=`当前85%语速含课间约 ${fmt(course.timingSummary.playbackTiming.duration)}；提问与练习按原定真实秒数。孟晟助教另计30:00。ZZL/F音频仅本机保存。`;
 if(manifest)$('duration').textContent=`语速85% · 保持音高；含课间约 ${fmt(classroomDuration(manifest,.85))}。提问10秒、练习60秒保持不变；孟晟助教另计30:00。`;
 $('play').disabled=!manifest;$('seek').disabled=!manifest;
 await selectBoard(Math.min(Number(query.get('board')||0),course.boards.length-1),false);
 // First board ready: preload all later board MP3s in a bounded queue.
 if(manifest){const queue=manifest.boards.slice(board+1).filter(b=>b.file);let cursor=0;void Promise.all(Array.from({length:3},async()=>{while(cursor<queue.length&&n===courseEpoch){const b=queue[cursor++];try{await audioURL(b.file);}catch{}}}));}
}
async function selectBoard(index,resume=playIntent){const n=++generation;playIntent=resume;preparing=true;$('complete').disabled=true;playing=false;audio.pause();completedWall=0;board=Math.max(0,Math.min(course.boards.length-1,index));$('board-select').value=board;$('status').textContent='正在准备本板字迹与整块语音…';const b=course.boards[board];manuscript(b);
 const nextPrepared=b.kind==='break'?null:await prepareBoard(b,language);if(n!==generation)return;prepared=nextPrepared;if(prepared)prepared.total=course.boards.length;
 const item=manifest?.boards[board];disconnectClassroomAudio(audio);audio=new Audio();audio.preload='auto';audio.preservesPitch=true;audio.playbackRate=classroomAudioRate(item,0,.85);requestedTime=0;
 if(item?.file){const src=await audioURL(item.file);if(n!==generation)return;audio.src=src;await new Promise((resolve,reject)=>{audio.addEventListener('loadedmetadata',resolve,{once:true});audio.addEventListener('error',()=>reject(Error('本板语音加载失败，可重试或换板')),{once:true});audio.load();});}
 if(n!==generation)return;preparing=false;$('complete').disabled=false;const target=audio,valid=()=>n===generation&&audio===target;finishCurrent=()=>{if(!valid()||!playIntent)return;const remaining=completedWall?5-(Date.now()-completedWall)/1000:0;if(remaining>0){setTimeout(finishCurrent,Math.min(1000,remaining*1000));return;}if(board<course.boards.length-1)selectBoard(board+1,true);else{playing=false;playIntent=false;update();}};audio.onended=finishCurrent;audio.onplay=()=>{if(valid()){playing=true;update()}};audio.onpause=()=>{if(valid()){playing=false;update()}};paint();if(playIntent&&item?.file)await playPrepared(audio,n);update();
}
function update(){$('play').textContent=playIntent?'暂停':'播放';$('status').textContent=`${course?.title||''} · ${board+1} / ${course?.boards.length||0} · ZZL / F${!manifest?' · 文本与板书预览':''}`;}
function paint(){if(!course)return;const b=course.boards[board],item=manifest?.boards[board],t=item?audio.currentTime:requestedTime,cx=$('board').getContext('2d');
 if(item){const rate=classroomAudioRate(item,t,.85);if(audio.playbackRate!==rate)audio.playbackRate=rate;}
 if(b.kind==='break'){cx.fillStyle='#06271c';cx.fillRect(0,0,1536,640);cx.fillStyle='#e4cf9c';cx.font='92px RefugeChinese';cx.textAlign='center';cx.fillText('课间休息',768,250);cx.font='88px sans-serif';cx.fillText(fmt(Math.min(300,Math.max(0,(item?.seconds||300)-t))),768,405);cx.textAlign='left';return;}
 if(!prepared)return;const fractions={};if(item){for(const w of item.writing)fractions[w.logical]=Math.max(fractions[w.logical]||0,Math.min(1,Math.max(0,(t-w.start)/(w.end-w.start))));}else Object.keys(prepared.logical).forEach(k=>fractions[k]=1);
 paintPrepared(cx,prepared,fractions);if(item&&t>=item.lastStrokeEnd){completedWall ||= Date.now()-Math.max(0,t-item.lastStrokeEnd)*1000;}else completedWall=0;const wait=item?.waits?.find(w=>t>=w.start&&t<w.end);if(wait){cx.fillStyle='#e4cf9c';cx.font='72px sans-serif';cx.textAlign='center';cx.fillText(fmt(Math.ceil(wait.end-t)),768,b.kind==='exercise'?425:575);cx.textAlign='left';}
 const cue=item?.cues?.find(w=>t>=w.start&&t<w.end);for(const e of $('script').querySelectorAll('article'))e.classList.toggle('active',e.dataset.line===cue?.lineId);
 if(item)$('seek').value=audio.currentTime/item.seconds*1000;
}
$('course').onchange=()=>loadCourse().catch(e=>$('status').textContent=e.message);$('board-select').onchange=e=>selectBoard(+e.target.value).catch(e=>$('status').textContent=e.message);
$('prev').onclick=()=>selectBoard(board-1).catch(e=>$('status').textContent=e.message);$('next').onclick=()=>selectBoard(board+1).catch(e=>$('status').textContent=e.message);
$('play').onclick=async()=>{if(!openingLocked&&board===0&&manifest?.openingSelection&&manifest.openingSelection.period!==openingPeriod())await loadCourse();openingLocked=true;if(!manifest){$('status').textContent='本板音频尚在生成，请先审阅逐行稿。';return;}playIntent=!playIntent;if(preparing){update();return;}if(!playIntent){audio.pause();}else{const b=manifest.boards[board];if(audio.ended||audio.currentTime>=b.seconds-.02){finishCurrent();update();return;}if(completedWall&&b.boardHoldSeconds>0&&audio.currentTime>=b.seconds-b.boardHoldSeconds)audio.currentTime=Math.min(b.seconds-.005,Math.max(audio.currentTime,b.lastStrokeEnd+(Date.now()-completedWall)/1000));await playPrepared();}update();};
$('complete').onclick=()=>{playIntent=false;audio.pause();playing=false;if(manifest)audio.currentTime=Math.max(0,manifest.boards[board].seconds-.01);requestedTime=Infinity;completedWall=Date.now();paint();update();};
$('lang').onclick=async()=>{const resume=playIntent,t=audio.currentTime;language=language==='zh'?'en':'zh';await selectBoard(board,resume);if(manifest)audio.currentTime=t;paint();};
$('seek').oninput=()=>{if(manifest){audio.currentTime=Number($('seek').value)/1000*manifest.boards[board].seconds;completedWall=audio.currentTime>=manifest.boards[board].lastStrokeEnd?Date.now():0;}paint();};
function frame(){paint();requestAnimationFrame(frame)}requestAnimationFrame(frame);
if(query.get('course'))$('course').value=query.get('course');
if(!query.has('measure'))loadCourse().catch(e=>{$('status').textContent=e.message;console.error(e)});
window.fClassroom={selectBoard,loadCourse,getState:()=>({board,playing,language,prepared,manifest,course,audio,output:classroomAudioOutputState()}),setTime:t=>{audio.pause();audio.currentTime=t;paint();}};
const focusPause=()=>{playIntent=false;audio.pause();};addEventListener('blur',focusPause);document.addEventListener('visibilitychange',()=>{if(document.hidden)focusPause();});
