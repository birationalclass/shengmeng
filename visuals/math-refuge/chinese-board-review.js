import {REPORTS} from './report-catalog.js';
import {createChineseChalk,paintChineseGroup} from './chinese-chalk.js?v=chinese36-1';
import {authoredContext,authoredFormula} from './authored-chalk.js?v=unframed-controls-1';
import {composeChalkPage} from './chalk-language.js?v=unframed-controls-1';
import {inkGuides,writingPlan,strokeReveal,rasterStrokeReveal,inkReveal} from './chalk-motion.js?v=hand-motion-2';
import {paintChalkStroke} from './chalk-annotations.js?v=report-line-sync-6';
import {drawClassroomMetadata} from './classroom-metadata.js?v=unframed-controls-1';
const $=id=>document.getElementById(id),canvas=$('board'),ctx=canvas.getContext('2d'),reports=[...REPORTS,{id:'km',speaker:'讨论班',topic:'极小模型纲领',manifest:'./assets/chalk/km/pages.json'}];
let library,pages=[],pageIndex=0,language='zh',full,rows=[],guides,plan,progress=1,playing=false,last=0;
async function image(url){const im=new Image();im.src=url;await im.decode();return im;}
async function preparePage(p,i,lang,authored=true){
 const pic=authored&&!p.kind&&!p.diagram?await authoredFormula(p.formulaAsset):await image(p.formulaAsset);
 const c=document.createElement('canvas');c.width=1536;c.height=640;const cx=c.getContext('2d'),chinese=lang==='zh'?await library.prepare(JSON.stringify(p)):null,recorder=authoredContext(cx,chinese,{latin:authored});
 const original=composeChalkPage(recorder.ctx,p,i,lang,pic,{deferStrokes:true,authored:true});const rows=recorder.rows(original),guides=inkGuides(cx.getImageData(0,0,1536,640),rows),plan=writingPlan(rows,guides);
 return {canvas:c,rows,guides,plan,original};
}
function render(){ctx.fillStyle='#193d33';ctx.fillRect(0,0,1536,640);if(!full)return;rows.forEach((r,i)=>{if(r.strokeRaster)paintChineseGroup(ctx,rows,i,j=>rasterStrokeReveal(rows,progress,j,guides));else if(r.strokePath)paintChalkStroke(ctx,strokeReveal(rows,progress,i,guides),r.chalkColor,r.strokeWidth);else{const w=inkReveal(rows,progress,i,guides);if(w>0){ctx.save();ctx.beginPath();ctx.rect(r[0],r[1],w,r[3]);ctx.clip();ctx.drawImage(full,0,0);ctx.restore();}}});drawClassroomMetadata(ctx,pages[pageIndex],pageIndex,language,{total:pages.length});$('seek').value=Math.round(progress*10000);$('play').textContent=playing?'暂停':'播放';$('status').textContent=(language==='zh'?'中文 · 36 鸿雷行书':'English')+' · '+Math.round(progress*100)+'% · '+(plan?.duration||0).toFixed(1)+' 秒';}
async function selectPage(i){playing=false;last=0;pageIndex=Math.max(0,Math.min(pages.length-1,i));$('status').textContent='正在准备本页字形…';const prepared=await preparePage(pages[pageIndex],pageIndex,language);full=prepared.canvas;rows=prepared.rows;guides=prepared.guides;plan=prepared.plan;progress=1;$('page').value=pageIndex;render();}
async function selectReport(id){const r=reports.find(r=>r.id===id);pages=(await fetch(r.manifest).then(r=>r.json())).pages;$('page').replaceChildren(...pages.map((p,i)=>{const o=document.createElement('option');o.value=i;o.textContent=(i+1)+' · '+p.title;return o}));$('report').value=id;await selectPage(0);}
try{
 await Promise.all(['42px RefugeChinese','42px RefugeLatin','42px RefugeMath'].map(f=>document.fonts.load(f)));library=await createChineseChalk();
 $('report').replaceChildren(...reports.map(r=>{const o=document.createElement('option');o.value=r.id;o.textContent=r.speaker+' · '+r.topic;return o}));await selectReport('ye2');await selectPage(5);
 $('report').onchange=e=>selectReport(e.target.value);$('page').onchange=e=>selectPage(Number(e.target.value));$('lang').onclick=async()=>{language=language==='zh'?'en':'zh';await selectPage(pageIndex)};$('complete').onclick=()=>{playing=false;progress=1;render()};$('restart').onclick=()=>{playing=false;last=0;progress=0;render()};$('play').onclick=()=>{if(progress>=1)progress=0;playing=!playing;last=0;render()};$('seek').oninput=()=>{playing=false;progress=Number($('seek').value)/10000;render()};
 function frame(now){if(playing&&!document.hidden){if(last)progress=Math.min(1,progress+(now-last)/1000*Number($('speed').value)/plan.duration);if(progress>=1)playing=false;render();}last=playing?now:0;requestAnimationFrame(frame)}requestAnimationFrame(frame);
 window.chineseBoardReview={library,reports,preparePage,selectReport,selectPage,setProgress:p=>{playing=false;progress=p;render()},setLanguage:async lang=>{language=lang;await selectPage(pageIndex)},getState:()=>({language,pageIndex,rows,plan,progress})};window.chineseBoardReady=true;
}catch(e){$('status').textContent='加载失败：'+e.message;window.chineseBoardError=e.message;throw e;}
