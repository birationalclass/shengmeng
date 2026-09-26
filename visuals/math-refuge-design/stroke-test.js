import {inkGuides,writingPlan,writingPose,inkReveal} from './chalk-motion.js?v137';
// Authored centreline strokes. These are not outlines extracted from a font.
import * as originalHand from './handwriting-glyphs.js?v66-galaxy';
import * as refinedHand from './refined-handwriting.js?v1';
const handStyle=new URLSearchParams(location.search).get('hand')==='original'?'original':'refined';
const {glyphs,advance}=handStyle==='original'?originalHand:refinedHand;
const ns='http://www.w3.org/2000/svg',library=new Map();
for(const [char,paths]of Object.entries(glyphs))library.set(char,paths.map(d=>{const p=document.createElementNS(ns,'path');p.setAttribute('d',d);const len=p.getTotalLength(),n=Math.max(4,Math.ceil(len/2)),a=[];for(let i=0;i<=n;i++){const q=p.getPointAtLength(len*i/n);a.push([q.x,q.y]);}return a;}));
const strokes=[],rows=[],textOps=[];let row=0,id=0;
function add(points,size){strokes.push({points,width:Math.max(handStyle==='refined'?1.7:1.45,size*(handStyle==='refined'?.058:.05)),row,seed:id++});}
function text(value,x,y,size=40){const op={value,x,y,size,row};textOps.push(op);for(const char of value){if(char!==' '){if(!library.has(char))throw Error('Missing authored strokes: '+char);for(const path of library.get(char))add(path.map(([a,b])=>[x+a*size/75,y+(b-72)*size/75]),size);}x+=(advance[char]||(handStyle==='refined'?60:65))*size/75;}op.width=x-op.x;return x;}
function fraction(top,bottom,x,y,size=36){const width=s=>[...s].reduce((w,c)=>w+(advance[c]||(handStyle==='refined'?60:65))*size/75,0);const w=Math.max(width(top),width(bottom))+18;text(top,x+(w-width(top))/2,y-15,size);add(Array.from({length:Math.ceil(w/2)+1},(_,i)=>{const t=i/Math.ceil(w/2);return[x+w*t,y+Math.sin(t*Math.PI*2+.5)*.55];}),size);strokes.at(-1).bar=true;text(bottom,x+(w-width(bottom))/2,y+size+16,size);return x+w+15;}
function line(fn){const begin=strokes.length;fn();const pts=strokes.slice(begin).flatMap(s=>s.points);const xs=pts.map(p=>p[0]),ys=pts.map(p=>p[1]);rows.push([Math.min(...xs)-5,Math.min(...ys)-5,Math.max(...xs)-Math.min(...xs)+10,Math.max(...ys)-Math.min(...ys)+10]);row++;}
function authorPage(text,fraction,line){
line(()=>{let x=text('P = p',87,135,38);text('g',x-5,147,25);x=text('(X) > 243,',x+25,135,38);x=text('s ≥ 9 ⇒ 1 +',x+22,135,38);x=fraction('1','s',x+4,122,30);x=text('≤',x+10,135,38);fraction('10','9',x,122,30);});

line(()=>{let x=text('d ≤',87,239,40);x=fraction('64P(1+1/s)','P−3',x,220,36);x=text('≤',x+24,239,40);fraction('640P','9(P−3)',x+8,220,36);});
line(()=>{let x=fraction('640P','9(P−3)',87,325,36);text('< 72 ⇔ 640P < 648(P−3)',x+20,344,40);});
line(()=>text('648(P−3)−640P = 8(P−243) > 0',87,435,39));
line(()=>text('Thus this case gives a strict bound below 72.',87,515,29));
line(()=>text('Equality can occur only in the small fibre-genus branch.',87,586,27));
}
authorPage(text,fraction,line);
const bodyEnd=strokes.length;text('Proposition 3.2 · The threshold 243',84,62,30);const titleStrokes=strokes.splice(bodyEnd);
const board=document.querySelector('#board'),ctx=board.getContext('2d'),tip=document.querySelector('#chalk'),status=document.querySelector('#status'),metrics=document.querySelector('#metrics'),progress=document.querySelector('#progress'),mode=document.querySelector('#mode'),play=document.querySelector('#play');
const fontChoice=document.querySelector('#fontChoice');fontChoice.value=handStyle;
const sizeControl=document.querySelector('#formulaSize');let formulaScale=.9;
function scaled(p,row){const k=row<4?formulaScale:1,base=[135,239,344,435][row]||0;return[87+(p[0]-87)*k,base+(p[1]-base)*k];}
const full=document.createElement('canvas');full.width=1536;full.height=640;const fc=full.getContext('2d');
function pressure(s,t){return s.width*(.78+.16*Math.sin(t*Math.PI)+.08*Math.sin(t*13+s.seed));}
function segment(c,a,b,width,color='#eee9d5'){c.lineCap='round';c.lineJoin='round';c.strokeStyle=color;c.lineWidth=width;c.beginPath();c.moveTo(...a);c.lineTo(...b);c.stroke();}
for(const stroke of strokes)for(let i=1;i<stroke.points.length;i++)segment(fc,stroke.points[i-1],stroke.points[i],pressure(stroke,i/stroke.points.length));
const started=performance.now(),packed=[],segments=[];let elapsed=0,previous=null;
function push(a,b,seconds,contact,width,row){segments.push({a,b,start:elapsed,end:elapsed+seconds,contact,width,row});elapsed+=seconds;}
for(const stroke of strokes){
 const p=stroke.points;if(previous)push(previous,p[0],.07+Math.min(.38,Math.hypot(p[0][0]-previous[0],p[0][1]-previous[1])/900),false,0,stroke.row);
 for(let i=1;i<p.length;i++){
  const a=p[i-1],b=p[i],dx=b[0]-a[0],dy=b[1]-a[1],length=Math.hypot(dx,dy);let bend=0;
  if(i>1){const c=p[i-2],pl=Math.hypot(a[0]-c[0],a[1]-c[1]);if(pl*length>0)bend=Math.acos(Math.max(-1,Math.min(1,((a[0]-c[0])*dx+(a[1]-c[1])*dy)/(pl*length))));}
  const width=pressure(stroke,i/p.length);push(a,b,length/(360/(1+bend*2.2)),true,width,stroke.row);packed.push(b[0],b[1],elapsed,width);
 }
 previous=p.at(-1);
}
const points=new Float32Array(packed),duration=elapsed,prepareMs=performance.now()-started,guides=inkGuides(fc.getImageData(0,0,1536,640),rows);writingPlan(rows,guides);
let t=0,playing=true,last=0,cursor=0,drawn=0,frames=[],raf=0;
function reset(){ctx.clearRect(0,0,1536,640);for(const stroke of titleStrokes)for(let i=1;i<stroke.points.length;i++)segment(ctx,stroke.points[i-1],stroke.points[i],pressure(stroke,i/stroke.points.length),'#e0cb9b');cursor=0;drawn=0;}
function pose(time){let lo=0,hi=segments.length-1;while(lo<hi){const m=(lo+hi)>>1;if(segments[m].end<time)lo=m+1;else hi=m;}const s=segments[lo],f=Math.max(0,Math.min(1,(time-s.start)/(s.end-s.start||1)));return {x:s.a[0]+(s.b[0]-s.a[0])*f,y:s.a[1]+(s.b[1]-s.a[1])*f,contact:s.contact,row:s.row,lift:Math.sin(f*Math.PI)};}
function render(time,seek=false){
 if(seek||time<drawn)reset();
 if(mode.value==='stroke'){
  while(cursor<segments.length&&segments[cursor].start<time){const s=segments[cursor],from=Math.max(drawn,s.start),to=Math.min(time,s.end);if(s.contact&&to>from){const f=(from-s.start)/(s.end-s.start),g=(to-s.start)/(s.end-s.start);segment(ctx,scaled([s.a[0]+(s.b[0]-s.a[0])*f,s.a[1]+(s.b[1]-s.a[1])*f],s.row),scaled([s.a[0]+(s.b[0]-s.a[0])*g,s.a[1]+(s.b[1]-s.a[1])*g],s.row),s.width*(s.row<4?formulaScale:1));}if(time<s.end)break;cursor++;}
 }else{reset();rows.forEach(([x,y,w,h],i)=>{const visible=inkReveal(rows,time/duration,i,guides);if(visible>0){const [sx,sy]=scaled([x,y],i),k=i<4?formulaScale:1;ctx.drawImage(full,x,y,visible,h,sx,sy,visible*k,h*k);}});}
 drawn=time;const p=mode.value==='stroke'?pose(time):writingPose(rows,time/duration,guides),scale=board.clientWidth/1536;const [tipX,tipY]=scaled([p.x,p.y],p.row);
 tip.style.transform=`translate(${tipX*scale}px,${tipY*scale-(p.contact?0:10+12*(p.lift||0))}px) rotate(-32deg) scale(${p.contact?1:1.07})`;tip.style.opacity=time>=duration?'0':p.contact?'1':'.58';
 progress.value=String(Math.round(time/duration*1000));status.textContent=`${(time/duration*100).toFixed(0)}% · ${time>=duration?'完成':p.contact?'落笔':'抬笔移位'} · ${duration.toFixed(1)} 秒`;
}
function stats(){const sorted=[...frames].sort((a,b)=>a-b),avg=frames.reduce((a,b)=>a+b,0)/(frames.length||1);metrics.textContent=`${strokes.length} 笔 · ${points.length/4} 采样点 · 紧凑轨迹 ${(points.byteLength/1024).toFixed(1)} KiB（不含页面和索引对象） · 时间轴准备 ${prepareMs.toFixed(1)} ms · 单帧书写 CPU 平均 ${avg.toFixed(2)} / P95 ${(sorted[Math.floor(sorted.length*.95)]||0).toFixed(2)} ms · ${frames.length} 帧样本`;}
function frame(now){if(playing&&!document.hidden){if(last)t=Math.min(duration,t+Math.min(.05,(now-last)/1000)*Number(document.querySelector('#speed').value));const begin=performance.now();render(t);frames.push(performance.now()-begin);if(frames.length>600)frames.shift();if(frames.length%30===0)stats();if(t===duration){playing=false;play.textContent='播放';stats();}}last=now;raf=requestAnimationFrame(frame);}
play.onclick=()=>{if(t>=duration){t=0;reset();}playing=!playing;play.textContent=playing?'暂停':'播放';last=0;};
progress.oninput=()=>{playing=false;play.textContent='播放';t=Number(progress.value)/1000*duration;render(t,true);stats();};
fontChoice.onchange=()=>{const url=new URL(location.href);url.searchParams.set('hand',fontChoice.value);location.href=url.href;};
sizeControl.oninput=()=>{formulaScale=Number(sizeControl.value)/100;document.querySelector('#formulaSizeValue').textContent=sizeControl.value+'%';render(t,true);};
mode.onchange=()=>{frames=[];render(t,true);stats();};document.addEventListener('visibilitychange',()=>last=0);window.addEventListener('resize',()=>render(t,true));
reset();render(0);stats();
const invalid=strokes.filter(s=>s.points.some(([x,y])=>!Number.isFinite(x+y)||x<0||x>1536||y<75||y>632));document.querySelector('#validation').textContent=`校验：${invalid.length===0?'全部轨迹位于书写区域内':'发现越界'}；每笔有独立抬笔段，回看时重建同一笔迹。`;board.dataset.validation=String(invalid.length);requestAnimationFrame(frame);
