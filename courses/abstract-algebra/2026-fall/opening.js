
(()=>{
'use strict';
const dialog=document.getElementById('courseOpening');
const pending=document.documentElement.classList;
let ready=false,started=false;
function openOpening(){if(!dialog.open){dialog.showModal();document.body.classList.add('opening-active')}pending.remove('course-opening-pending');if(!started){started=true;initialize().catch(()=>{document.querySelector('[data-loading-label]').textContent='请直接进入课程查看课表';document.querySelector('[data-loading-percent]').textContent='';})}}
function leaveOpening(){dialog.close();document.body.classList.remove('opening-active');pending.remove('course-opening-pending');const main=document.getElementById('main');main.setAttribute('tabindex','-1');main.focus({preventScroll:true})}
dialog.querySelector('[data-enter-course]').addEventListener('click',leaveOpening);
dialog.addEventListener('cancel',e=>{e.preventDefault();leaveOpening()});
document.querySelector('[data-replay-opening]').addEventListener('click',openOpening);
function report(value){const bar=dialog.querySelector('progress');bar.value=value;dialog.querySelector('[data-loading-percent]').textContent=value+'%'}
const paint=()=>new Promise(resolve=>requestAnimationFrame(()=>requestAnimationFrame(resolve)));
async function initialize(){
const root=document.getElementById('symmetry-particle-studies'),canvas=root.querySelector('canvas'),buttons=[...root.querySelectorAll('[data-pattern]')],tourButton=root.querySelector('[data-tour]'),slider=root.querySelector('[data-morph]'),status=root.querySelector('[data-status]');
const gl=canvas.getContext('webgl',{alpha:false,antialias:false,preserveDrawingBuffer:true});
if(!gl)throw new Error('WebGL unavailable');
report(10);await paint();
const TAU=Math.PI*2,N=48000;
const names=[['六瓣玫瑰','SIXFOLD ROSETTE',6],['八角星','OCTAGRAM',8],['十二重花窗','TWELVEFOLD TRACERY',12]];
let rs=862413;function random(){rs=(Math.imul(rs,1664525)+1013904223)>>>0;return rs/4294967296}function normal(){return Math.sqrt(-2*Math.log(Math.max(1e-8,random())))*Math.cos(TAU*random())}
function pointOnPolygon(n,step,t,r,phase){let edge=Math.floor(t*n),f=t*n-edge,a=TAU*edge/n+phase,b=TAU*(edge+step)/n+phase;return [r*((1-f)*Math.cos(a)+f*Math.cos(b)),r*((1-f)*Math.sin(a)+f*Math.sin(b))]}
function point(kind){const u=random(),t=random()*TAU;let x,y,r;
if(kind===0){
 if(u<.50){let k=Math.floor(random()*6),a=k*TAU/6;let lx=.385+.388*Math.cos(t),ly=.171*Math.sin(t);x=lx*Math.cos(a)-ly*Math.sin(a);y=lx*Math.sin(a)+ly*Math.cos(a)}
 else if(u<.70){r=.51+.22*Math.cos(6*t);x=r*Math.cos(t);y=r*Math.sin(t)}
 else if(u<.81){r=.23+.055*Math.cos(6*t);x=r*Math.cos(t);y=r*Math.sin(t)}
 else if(u<.94){r=random()<.6?.86:.902;x=r*Math.cos(t);y=r*Math.sin(t)}
 else if(u<.98){let k=Math.floor(random()*12),a=k*TAU/12;r=.035; x=.83*Math.cos(a)+r*Math.cos(t);y=.83*Math.sin(a)+r*Math.sin(t)}
 else{r=Math.sqrt(random())*.98;x=r*Math.cos(t);y=r*Math.sin(t)}
}else if(kind===1){
 if(u<.54){[x,y]=pointOnPolygon(8,3,random(),.89,Math.PI/8)}
 else if(u<.74){[x,y]=pointOnPolygon(8,3,random(),.51,0)}
 else if(u<.85){r=random()<.62?.942:.973;x=r*Math.cos(t);y=r*Math.sin(t)}
 else if(u<.94){[x,y]=pointOnPolygon(8,1,random(),.76,Math.PI/8)}
 else if(u<.98){r=.16;x=r*Math.cos(t);y=r*Math.sin(t)}
 else{r=Math.sqrt(random())*.99;x=r*Math.cos(t);y=r*Math.sin(t)}
}else{
 if(u<.43){let k=Math.floor(random()*12),a=k*TAU/12,lx=.49+.326*Math.cos(t),ly=.103*Math.sin(t);x=lx*Math.cos(a)-ly*Math.sin(a);y=lx*Math.sin(a)+ly*Math.cos(a)}
 else if(u<.68){let k=Math.floor(random()*12),a=k*TAU/12;x=.655*Math.cos(a)+.23*Math.cos(t);y=.655*Math.sin(a)+.23*Math.sin(t)}
 else if(u<.79){r=.306+.079*Math.cos(12*t);x=r*Math.cos(t);y=r*Math.sin(t)}
 else if(u<.94){r=random()<.62?.926:.956;x=r*Math.cos(t);y=r*Math.sin(t)}
 else if(u<.98){r=.122;x=r*Math.cos(t);y=r*Math.sin(t)}
 else{r=Math.sqrt(random())*.98;x=r*Math.cos(t);y=r*Math.sin(t)}
}
const spread=u>.98?.012:(random()<.92?.0034:.011);return[x+normal()*spread,y+normal()*spread];}
// Each design is sampled in a fundamental sector, then reflected and rotated.
// The target point sets have exact D6, D8 and D12 symmetry, including their grain scatter.
function makePattern(kind){const order=names[kind][2],baseCount=N/(2*order),out=[];
 for(let i=0;i<baseCount;i++){let [x,y]=point(kind),r=Math.hypot(x,y),a=Math.acos(Math.max(-1,Math.min(1,Math.cos(order*Math.atan2(y,x)))))/order;
  for(let j=0;j<order;j++)for(let sign of [-1,1]){let q=j*TAU/order+sign*a;out.push([r*Math.cos(q),r*Math.sin(q),q,r]);}
 }
 // Angular ordering gives persistent particle identities a short, coherent route.
 out.sort((a,b)=>a[2]-b[2]||a[3]-b[3]);let result=new Float32Array(N*2);for(let i=0;i<N;i++){result[2*i]=out[i][0];result[2*i+1]=out[i][1]}return result;}
const targets=[];for(let i=0;i<3;i++){targets.push(makePattern(i));report(25+i*20);await paint();}
const vertex=`precision highp float;attribute vec2 start;attribute vec2 finish;attribute vec4 grain;uniform float progress;uniform float aspect;uniform float dpr;varying vec3 color;varying float opacity;varying float facet;
void main(){float t=progress;float e=t*t*t*(t*(t*6.-15.)+10.);vec2 delta=finish-start;float arch=sin(3.14159265359*e);vec2 p=mix(start,finish,e)+vec2(-delta.y,delta.x)*arch*.28;float dist=length(delta);p+=vec2(sin(grain.x*19.+e*6.283),cos(grain.y*23.-e*6.283))*arch*min(.022,dist*.16);
float fit=min(1.,aspect)*.78;p*=fit;p.y+=.06;p.x/=aspect;gl_Position=vec4(p,0.,1.);gl_PointSize=(.75+grain.z*1.5)*dpr;
float light=.66+.34*clamp(1.-length(p-vec2(-.35,.48))*.5,0.,1.);vec3 base=mix(vec3(.42,.29,.13),vec3(.84,.69,.40),grain.w);base=mix(base,vec3(.98,.88,.64),pow(grain.y,18.)*.66);color=base*light;opacity=.65+.30*grain.x;facet=grain.z;}`;
const fragment=`precision mediump float;varying vec3 color;varying float opacity;varying float facet;void main(){vec2 p=gl_PointCoord*2.-1.;float r=length(p*vec2(1.,.84+facet*.22));if(r>1.)discard;float edge=1.-smoothstep(.25,1.,r);float shading=.74+.26*clamp(.5-p.x*.5+p.y*.2,0.,1.);gl_FragColor=vec4(color*shading,edge*opacity);}`;
const bgv=`attribute vec2 pos;varying vec2 uv;void main(){uv=pos;gl_Position=vec4(pos,0.,1.);}`;
const bgf=`precision highp float;varying vec2 uv;uniform vec2 dimensions;float hash(vec2 p){return fract(sin(dot(p,vec2(127.1,311.7)))*43758.5453);}void main(){float noise=hash(floor(gl_FragCoord.xy))*.009;float lamp=exp(-length((uv-vec2(-.5,.45))*vec2(.7,1.)))*.015;float v=1.-smoothstep(.25,1.5,length(uv));gl_FragColor=vec4(vec3(.018,.017,.014)+vec3(.6,.49,.28)*(lamp+noise)*v,1.);}`;
function compile(type,src){let s=gl.createShader(type);gl.shaderSource(s,src);gl.compileShader(s);if(!gl.getShaderParameter(s,gl.COMPILE_STATUS))throw Error(gl.getShaderInfoLog(s));return s}
function link(v,f){let p=gl.createProgram();gl.attachShader(p,compile(gl.VERTEX_SHADER,v));gl.attachShader(p,compile(gl.FRAGMENT_SHADER,f));gl.linkProgram(p);if(!gl.getProgramParameter(p,gl.LINK_STATUS))throw Error(gl.getProgramInfoLog(p));return p}
const program=link(vertex,fragment),bg=link(bgv,bgf),quad=gl.createBuffer();gl.bindBuffer(gl.ARRAY_BUFFER,quad);gl.bufferData(gl.ARRAY_BUFFER,new Float32Array([-1,-1,1,-1,-1,1,-1,1,1,-1,1,1]),gl.STATIC_DRAW);
function makeBuffer(data,usage){let b=gl.createBuffer();gl.bindBuffer(gl.ARRAY_BUFFER,b);gl.bufferData(gl.ARRAY_BUFFER,data,usage);return b}
report(82);await paint();
let source=targets[0].slice(),destination=targets[0];const srcBuffer=makeBuffer(source,gl.DYNAMIC_DRAW),dstBuffer=makeBuffer(destination,gl.DYNAMIC_DRAW);let seedData=new Float32Array(N*4);for(let i=0;i<seedData.length;i++)seedData[i]=random();const seedBuffer=makeBuffer(seedData,gl.STATIC_DRAW);
const loc={s:gl.getAttribLocation(program,'start'),f:gl.getAttribLocation(program,'finish'),g:gl.getAttribLocation(program,'grain'),u:gl.getUniformLocation(program,'progress'),a:gl.getUniformLocation(program,'aspect'),d:gl.getUniformLocation(program,'dpr'),q:gl.getAttribLocation(bg,'pos')};
function attribute(buffer,location,size){gl.bindBuffer(gl.ARRAY_BUFFER,buffer);gl.enableVertexAttribArray(location);gl.vertexAttribPointer(location,size,gl.FLOAT,false,0,0)}
let amount=1,selected=0,animating=false,tour=false,tourPaused=false,tourQueue=[],holdUntil=0,raf=0,last=0;const duration=3900;
function ease(t){return t*t*t*(t*(t*6-15)+10)}
function snapshot(){const e=ease(amount),arch=Math.sin(Math.PI*e),p=new Float32Array(N*2);for(let i=0;i<N;i++){let k=2*i,dx=destination[k]-source[k],dy=destination[k+1]-source[k+1],scatter=arch*Math.min(.022,Math.hypot(dx,dy)*.16);p[k]=source[k]+dx*e-dy*arch*.28+Math.sin(seedData[i*4]*19+e*TAU)*scatter;p[k+1]=source[k+1]+dy*e+dx*arch*.28+Math.cos(seedData[i*4+1]*23-e*TAU)*scatter}return p}
function updateLabels(){root.querySelector('[data-index]').textContent=String(selected+1).padStart(2,'0');root.querySelector('[data-name]').textContent=names[selected][0];root.querySelector('[data-en]').textContent=names[selected][1];root.querySelector('[data-symmetry]').textContent=names[selected][2]+' 重旋转 · 镜面对称';buttons.forEach((b,i)=>b.setAttribute('aria-pressed',String(i===selected)));root.querySelector('[data-announcement]').textContent='正在显示'+names[selected][0];}
function draw(){const rect=canvas.getBoundingClientRect(),ratio=Math.min(2,window.devicePixelRatio||1),w=Math.max(1,Math.round(rect.width*ratio)),h=Math.max(1,Math.round(rect.height*ratio));if(canvas.width!==w||canvas.height!==h){canvas.width=w;canvas.height=h}gl.viewport(0,0,w,h);gl.disable(gl.BLEND);gl.useProgram(bg);attribute(quad,loc.q,2);gl.drawArrays(gl.TRIANGLES,0,6);gl.useProgram(program);attribute(srcBuffer,loc.s,2);attribute(dstBuffer,loc.f,2);attribute(seedBuffer,loc.g,4);gl.enable(gl.BLEND);gl.blendFunc(gl.SRC_ALPHA,gl.ONE_MINUS_SRC_ALPHA);gl.uniform1f(loc.u,amount);gl.uniform1f(loc.a,w/h);gl.uniform1f(loc.d,ratio);gl.drawArrays(gl.POINTS,0,N);slider.value=amount;status.textContent=amount>=1?'已成形':Math.round(amount*100)+'%';root.dataset.activePattern=selected;root.dataset.progress=amount.toFixed(4);root.dataset.particleCount=N;}
function upload(){gl.bindBuffer(gl.ARRAY_BUFFER,srcBuffer);gl.bufferSubData(gl.ARRAY_BUFFER,0,source);gl.bindBuffer(gl.ARRAY_BUFFER,dstBuffer);gl.bufferSubData(gl.ARRAY_BUFFER,0,destination);}
function stopTour(){tourPaused=false;tour=false;tourQueue=[];holdUntil=0;tourButton.textContent='连续预览';}
function moveTo(index,now){source=snapshot();destination=targets[index];selected=index;amount=0;last=now;animating=true;upload();updateLabels();draw();}
function start(){cancelAnimationFrame(raf);last=0;raf=requestAnimationFrame(tick)}
function tick(now){if(animating){if(last)amount=Math.min(1,amount+(now-last)/duration);last=now;draw();if(amount===1){animating=false;holdUntil=now+2100;}}
 else if(tour){if(!holdUntil)holdUntil=now+1500;if(now>=holdUntil){if(tourQueue.length){moveTo(tourQueue.shift(),now);holdUntil=0}else{stopTour();last=0;return}}}
 if(animating||tour)raf=requestAnimationFrame(tick);else last=0;}
buttons.forEach((b,i)=>b.addEventListener('click',()=>{stopTour();if(i===selected&&amount===1)return;moveTo(i,performance.now());start()}));
tourButton.addEventListener('click',()=>{if(tour){tour=false;tourPaused=true;cancelAnimationFrame(raf);last=0;tourButton.textContent='继续预览';return}if(tourPaused){tourPaused=false;tour=true;holdUntil=0;tourButton.textContent='暂停预览';start();return}tour=true;tourQueue=[(selected+1)%3,(selected+2)%3];holdUntil=0;tourButton.textContent='暂停预览';start()});
slider.addEventListener('input',()=>{stopTour();animating=false;cancelAnimationFrame(raf);amount=Number(slider.value);last=0;draw()});
document.addEventListener('visibilitychange',()=>{last=0;holdUntil=0;});new ResizeObserver(draw).observe(canvas);updateLabels();report(96);draw();await paint();report(100);ready=true;root.dataset.ready='true';await paint();dialog.classList.add('opening-ready');dialog.querySelector('[data-loading]').hidden=true;
if(dialog.open&&!matchMedia('(prefers-reduced-motion: reduce)').matches)tourButton.click();
dialog.addEventListener('close',()=>{stopTour();animating=false;cancelAnimationFrame(raf);last=0;});
// Compact, read-only evidence for continuity and point-set symmetry verification.
root._particleEvidence=()=>({count:N,selected,progress:amount,positions:snapshot(),targets});
}
if(!location.hash)openOpening();else pending.remove('course-opening-pending');
})();
