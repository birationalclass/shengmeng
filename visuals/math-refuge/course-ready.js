import {resourceFetch} from './resource-fetch.js';
// One startup owner: the Refuge classroom sequence, with an explicit whole-course gate.
export async function prepareCourseBoardFiles(page,fetcher=resourceFetch){
 const board=page.orderedBoard,files=board?board.rows.flatMap(row=>[...(row.tokens||[]),...(row.enTokens||[])].map(t=>t.asset).filter(Boolean)):[page.formulaAsset].filter(Boolean);
 if(board?.diagramAsset)files.push(board.diagramAsset);
 const unique=[...new Set(files)];let next=0;
 await Promise.all(Array.from({length:Math.min(2,unique.length)},async()=>{while(next<unique.length){const response=await fetcher(unique[next++]);if(!response.ok)throw Error('板书资源下载未完成');await response.arrayBuffer();}}));
}
export async function startReadyCourse(lecture,id,{autoplay=true,onSelected=()=>{},onProgress=()=>{}}={}){
 const retry=lecture.hasSelection&&lecture.report.id===id&&lecture.voiceManifest&&lecture.courseLoadState?.phase==='error';
 lecture.beginCoursePreparation();
 try{
  if(!retry&&!await lecture.setReport(id,{autoplay:false}))throw Error('课程未准备好');
  await lecture.setLanguage('zh');
  onSelected();
  await lecture.prepareCourse(onProgress);
  lecture.setVoiceRate(lecture.report.narration?.defaultPlaybackRate??lecture.voiceManifest?.policy?.defaultPlaybackRate??1);
  if(!await lecture.voiceSeek(0))throw Error('开场语音定位失败');
  lecture.finishCoursePreparation();
  if(autoplay)await lecture.toggleVoice();
  return true;
 }catch(error){lecture.failCoursePreparation(error);throw error;}
}

export async function prepareWholeCourse({count,prepareBoard,prepareVoice,prefetchAudio,audioState,onProgress=()=>{},delay=ms=>new Promise(r=>setTimeout(r,ms))}){
 let boards=0,done=false,failed=false,lastRatio=0;
 const report=()=>{const audio=audioState(),total=count+(audio.total||0)+1,completed=boards+(audio.completed||0);lastRatio=Math.max(lastRatio,Math.min(.99,completed/total));onProgress({phase:'loading',ratio:lastRatio,boards,totalBoards:count,audio:audio.completed||0,totalAudio:audio.total||0});};
 report();
 if(!await prepareVoice())throw Error('开场语音未就绪，请重试');
 const audioJob=Promise.resolve(prefetchAudio()).then(state=>{if(state?.phase!=='ready')throw Error('语音下载未完成，请重试');});
 const boardJob=(async()=>{for(let i=0;i<count&&!failed;i++){if(!await prepareBoard(i))throw Error('第'+(i+1)+'块板书未就绪');boards++;report();}})();
 const watch=(async()=>{while(!done){report();await delay(150);}})();
 try{await Promise.all([audioJob,boardJob]);done=true;await watch;onProgress({phase:'ready',ratio:1,boards,totalBoards:count,audio:audioState().completed||0,totalAudio:audioState().total||0});return true;}
 catch(error){failed=true;done=true;await Promise.allSettled([watch,boardJob]);throw error;}
}

export function paintCourseLoading(ctx,width,height,state){
 const x=width/2,y=height*.43,r=height*.17,p=Math.max(0,Math.min(1,state.ratio||0));
 ctx.save();ctx.fillStyle='#193d33';ctx.fillRect(0,0,width,height);
 ctx.lineWidth=7;ctx.strokeStyle='#eee9d52b';ctx.beginPath();ctx.arc(x,y,r,0,Math.PI*2);ctx.stroke();
 ctx.strokeStyle=state.error?'#ffccac':'#eee9d5';ctx.lineCap='round';ctx.beginPath();ctx.arc(x,y,r,-Math.PI/2,-Math.PI/2+Math.PI*2*p);ctx.stroke();
 ctx.textAlign='center';ctx.textBaseline='middle';ctx.fillStyle='#eee9d5';ctx.font='52px RefugeLatin, RefugeChinese, sans-serif';ctx.fillText(Math.floor(p*100)+'%',x,y);
 ctx.font='30px RefugeChinese, sans-serif';ctx.fillText(state.error?'加载未完成 · 点击黑板重试':'正在准备整课板书与语音',x,height*.73);
 ctx.font='22px RefugeChinese, sans-serif';ctx.fillStyle='#e4cf9c';ctx.fillText(state.error?'保留已下载资源，重试后继续':`板书 ${state.boards||0} / ${state.totalBoards||'…'}    语音 ${state.audio||0} / ${state.totalAudio||'…'}`,x,height*.83);
 ctx.restore();
}
