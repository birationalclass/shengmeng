const mode=new URLSearchParams(location.search).get('quality')||'balanced';
const optimized=true;
const profile=mode==='light'?{pixels:900,steps:400,octaves:3}:{pixels:1200,steps:520,octaves:4};
if(optimized)await new Promise(resolve=>requestAnimationFrame(()=>requestAnimationFrame(resolve)));
const T=await import('../../../visuals/3d/vendor/three.module.js');
// Independent preview: no changes to the production galaxy or account state.
const canvas=document.querySelector('canvas'),error=document.querySelector('#error');
window.addEventListener('error',e=>error.textContent=e.message);
window.addEventListener('unhandledrejection',e=>error.textContent=String(e.reason));
const renderer=new T.WebGLRenderer({canvas,antialias:false,powerPreference:'high-performance'});
const scene=new T.Scene(),camera=new T.Camera();
const uniforms={resolution:{value:new T.Vector2()},time:{value:0},eye:{value:new T.Vector3()},zoom:{value:1}};
const material=new T.ShaderMaterial({uniforms,vertexShader:`varying vec2 uv0;void main(){uv0=uv;gl_Position=vec4(position.xy,0.,1.);}`,fragmentShader:`
precision highp float;varying vec2 uv0;uniform vec2 resolution;uniform float time;uniform vec3 eye;uniform float zoom;
float hash(vec3 p){return fract(sin(dot(p,vec3(127.1,311.7,74.7)))*43758.5453);}
float noise(vec3 p){vec3 i=floor(p),f=fract(p);f=f*f*(3.-2.*f);return mix(mix(mix(hash(i),hash(i+vec3(1,0,0)),f.x),mix(hash(i+vec3(0,1,0)),hash(i+vec3(1,1,0)),f.x),f.y),mix(mix(hash(i+vec3(0,0,1)),hash(i+vec3(1,0,1)),f.x),mix(hash(i+vec3(0,1,1)),hash(i+vec3(1,1,1)),f.x),f.y),f.z);}
float fbm(vec3 p){float a=.5,n=0.;for(int k=0;k<${optimized?profile.octaves:4};k++){n+=a*noise(p);p=p*2.07+5.1;a*=.5;}return n;}
vec3 sky(vec3 d){float cloud=pow(fbm(d*4.+9.),4.);vec3 c=vec3(.012,.017,.027)*cloud;vec3 q=d*650.,cell=floor(q);float star=pow(max(0.,1.-length(fract(q)-.5)*2.),18.)*step(.997,hash(cell));return c+vec3(.52,.62,.8)*star*.7;}
float clouds(float r,float a,float height){
 float cycle=time/10.,age=fract(cycle)*10.;
 float a0=a-age*.95/pow(r/3.,1.5),a1=a-(age+10.)*.95/pow(r/3.,1.5);
 vec3 p0=vec3(cos(a0)*r*.85,sin(a0)*r*.85,height*2.+floor(cycle)*.71);
 vec3 p1=vec3(cos(a1)*r*.85,sin(a1)*r*.85,height*2.+(floor(cycle)-1.)*.71);
 return mix(fbm(p1),fbm(p0),smoothstep(0.,1.,fract(cycle)));
}
vec3 gas(vec3 p,vec3 v){
 float r=length(p.xz),a=atan(p.z,p.x);
 // Differential Kepler-like motion shears knots, rather than rotating a rigid texture.
 float phase=a-time*1.8/pow(r/3.,1.5),drift=r+time*.013;
 vec3 q=vec3(cos(phase)*12.,sin(phase)*12.,drift*9.);
 float large=fbm(vec3(cos(phase)*3.,sin(phase)*3.,r*2.));
 float thin=fbm(q+large*2.);float fibers=.5+.5*sin(r*65.+thin*8.+sin(phase*9.+r*3.)*.8);
  float cloud=clouds(r,a,0.);
 float billow=smoothstep(.25,.72,cloud);
 float gaps=smoothstep(.22,.5,cloud);
 float density=(.08+2.8*pow(billow,1.8))*(.18+.82*gaps)*(.8+.3*thin+.015*fibers);
 float heat=pow(3./r,.75)*pow(max(.001,1.-sqrt(3./r)),.25)*2.;
 vec3 color=mix(vec3(.64,.095,.015),vec3(1.,.72,.36),clamp(heat,0.,1.));color=mix(color,vec3(1.,.94,.79),smoothstep(.82,1.15,heat));
 vec3 tangent=normalize(vec3(-p.z,0.,p.x));float beta=sqrt(.5/(r-1.));
 float shift=sqrt(1.-1./r)*sqrt(1.-beta*beta)/(1.-beta*dot(tangent,-normalize(v)));
 float beam=clamp(pow(shift,3.),.16,3.5);
 float envelope=smoothstep(3.,3.25,r)*(1.-smoothstep(8.,12.,r))*pow(3./r,1.6);
 return color*density*envelope*beam*3.4;
}
uniform sampler2D frontMap;uniform sampler2D backMap;
vec3 mappedGas(vec4 hit){
 if(hit.w<.01)return vec3(0.);
 vec3 p=vec3(hit.x,0.,hit.y),tangent=normalize(vec3(-p.z,0.,p.x));
 // Reconstruct the tangential component needed by the Doppler shading.
 vec3 v=-tangent*hit.z+vec3(0.,sqrt(max(0.,1.-hit.z*hit.z)),0.);
 return gas(p,v)*hit.w;
}
void main(){
 vec4 front=texture2D(frontMap,uv0),back=texture2D(backMap,uv0);
 vec3 light=mappedGas(front)+mappedGas(back)*.12;
 light=vec3(1.)-exp(-light*1.15);light=pow(light,vec3(.82));
 gl_FragColor=vec4(light,1.);
}`});
const quad=new T.Mesh(new T.PlaneGeometry(2,2),material);scene.add(quad);
// Cache geometry separately from animated gas. No iterative tracing in animation frames.
const targets=[0,1].map(()=>new T.WebGLRenderTarget(1,1,{type:T.HalfFloatType,minFilter:T.NearestFilter,magFilter:T.NearestFilter,depthBuffer:false}));
uniforms.frontMap={value:targets[0].texture};uniforms.backMap={value:targets[1].texture};
const rayUniforms={...uniforms,layer:{value:0}};
const rayMaterial=new T.ShaderMaterial({uniforms:rayUniforms,vertexShader:material.vertexShader,fragmentShader:`
precision highp float;varying vec2 uv0;uniform vec2 resolution;uniform vec3 eye;uniform float zoom;uniform int layer;
vec3 acceleration(vec3 p,float h2){float r2=dot(p,p);return -1.5*h2*p/(r2*r2*sqrt(r2));}
void main(){
 vec2 xy=(uv0-.5)*2.;xy.x*=resolution.x/resolution.y;xy=mat2(.985,-.174,.174,.985)*xy;
 vec3 f=normalize(-eye),right=normalize(cross(f,vec3(0,1,0))),up=cross(right,f);
 vec3 p=eye,v=normalize(f+zoom*.43*(xy.x*right+xy.y*up));float h2=dot(cross(p,v),cross(p,v));int hits=0;
 gl_FragColor=vec4(0.);
 for(int i=0;i<240;i++){
  float r=length(p);if(r<1.005||r>55.)break;
  float ds=clamp(r*.065,.025,.8);vec3 old=p,oldV=v;
  vec3 halfV=v+acceleration(p,h2)*ds*.5,halfP=p+v*ds*.5;
  v+=acceleration(halfP,h2)*ds;p+=halfV*ds;
  if(old.y*p.y<0.){
   float fraction=old.y/(old.y-p.y);vec3 hit=mix(old,p,fraction);float radius=length(hit.xz);
   if(radius>3.&&radius<12.){
    if(hits==layer){vec3 tangent=normalize(vec3(-hit.z,0.,hit.x));gl_FragColor=vec4(hit.xz,dot(tangent,-normalize(mix(oldV,v,fraction))),1.);break;}
    hits++;
   }
  }
 }
}`});
let mapDirty=true,mapBuilds=0,frames=0,statsStart=performance.now(),lastMap=0;
function cacheRays(){quad.material=rayMaterial;for(let i=0;i<2;i++){rayUniforms.layer.value=i;renderer.setRenderTarget(targets[i]);renderer.render(scene,camera);}renderer.setRenderTarget(null);quad.material=material;mapDirty=false;mapBuilds++;}

let groupOrder=4;let azimuth=.25,elevation=.21,targetElevation=.21,targetAzimuth=.25,distance=29,paused=false,en=false,drag=null,last=performance.now();
function resize(){
 const narrow=innerWidth<700,aspect=innerWidth/innerHeight;
 const z=narrow?Math.max(37,10/(Math.tan(23*Math.PI/180)*aspect)):27;
 const depth=Math.hypot(narrow?0:1.2,narrow?16:12,z);
 const base=groupOrder<=8?.61:groupOrder<=24?.32:.17;
 // Match the production 8.5-unit billboard, identity scale 1.7, and 46-degree camera.
 const size=8.5*base*1.7*innerHeight/(2*depth*Math.tan(23*Math.PI/180));
 renderer.setPixelRatio(Math.min(devicePixelRatio,2));renderer.setSize(size*1.35,size*1.35);
 renderer.getDrawingBufferSize(uniforms.resolution.value);uniforms.zoom.value=1.35*22/(2*.43*29);
 const w=Math.ceil(uniforms.resolution.value.x);for(const target of targets)target.setSize(w,w);
 canvas.dataset.projectedSize=size.toFixed(1);mapDirty=true;
 document.querySelector('#actual-size').textContent=`${Math.round(size)} × ${Math.round(size)} px`;
}
for(const [id,order] of [['size4',4],['size24',24],['size120',120]])document.getElementById(id).onclick=()=>{groupOrder=order;resize();for(const k of ['size4','size24','size120'])document.getElementById(k).setAttribute('aria-pressed',String(k===id));};addEventListener('resize',resize);resize();
canvas.addEventListener('pointerdown',e=>{drag={x:e.clientX,y:e.clientY};canvas.setPointerCapture(e.pointerId);});
canvas.addEventListener('pointermove',e=>{if(!drag)return;targetAzimuth-=(e.clientX-drag.x)*.006;targetElevation=Math.max(-1.4,Math.min(1.4,targetElevation+(e.clientY-drag.y)*.005));drag={x:e.clientX,y:e.clientY};});
canvas.addEventListener('pointerup',()=>drag=null);canvas.addEventListener('pointercancel',()=>drag=null);
canvas.addEventListener('wheel',e=>{e.preventDefault();distance=Math.max(19,Math.min(45,distance+e.deltaY*.015));},{passive:false});
canvas.addEventListener('dblclick',()=>{targetElevation=.21;targetAzimuth=.25;distance=29;});
for(const [id,angle] of [['cinema',.21],['above',1.15],['edge',.045]])document.getElementById(id).onclick=()=>{targetElevation=angle;for(const k of ['cinema','above','edge'])document.getElementById(k).setAttribute('aria-pressed',String(k===id));};
function labels(){document.documentElement.lang=en?'en':'zh-CN';document.querySelector('h1').textContent=en?'BLACK HOLE · DISK':'黑洞 · 吸积盘';document.querySelector('header p').textContent=en?'Drag to orbit · Scroll to zoom · Double-click to reset':'拖动环绕 · 滚轮缩放 · 双击复位';document.querySelector('#cinema').textContent=en?'Oblique':'斜侧视角';document.querySelector('#above').textContent=en?'Above':'俯视盘面';document.querySelector('#edge').textContent=en?'Edge-on':'掠过盘面';document.querySelector('#pause').textContent=paused?(en?'▶ Play':'▶ 继续'):(en?'Ⅱ Pause':'Ⅱ 暂停');document.querySelector('#language').textContent=en?'中文':'EN';document.querySelector('footer').textContent=en?'Schwarzschild · Realtime ray integration / procedural gas study':'Schwarzschild · 实时光线积分 / 程序化气体实验';}
document.querySelector('#language').onclick=()=>{en=!en;labels();};
document.querySelector('#pause').onclick=e=>{paused=!paused;e.currentTarget.setAttribute('aria-pressed',String(paused));labels();};
document.querySelector('#fullscreen').onclick=()=>{(document.fullscreenElement?document.exitFullscreen():document.documentElement.requestFullscreen()).catch(e=>error.textContent=e.message);};
let lastDraw=0;
document.addEventListener('visibilitychange',()=>{last=performance.now();});
renderer.setAnimationLoop(now=>{
 if(document.hidden)return;
 const moving=Math.abs(targetElevation-elevation)+Math.abs(targetAzimuth-azimuth)>.0001;
 const nextEye=new T.Vector3(Math.sin(azimuth)*Math.cos(elevation)*distance,Math.sin(elevation)*distance,Math.cos(azimuth)*Math.cos(elevation)*distance);
 if(moving||nextEye.distanceToSquared(uniforms.eye.value)>.00001)mapDirty=true;
 if(paused&&!moving&&!mapDirty){last=now;return;}
 lastDraw=now;const dt=Math.min((now-last)/1000,.1);last=now;
 if(!paused)uniforms.time.value+=dt;
 const ease=1-Math.exp(-dt*8);elevation+=(targetElevation-elevation)*ease;azimuth+=(targetAzimuth-azimuth)*ease;
 uniforms.eye.value.set(Math.sin(azimuth)*Math.cos(elevation)*distance,Math.sin(elevation)*distance,Math.cos(azimuth)*Math.cos(elevation)*distance);
 if(mapDirty){cacheRays();lastMap=now;}
 renderer.render(scene,camera);frames++;
 if(now-statsStart>2000){canvas.dataset.fps=(frames*1000/(now-statsStart)).toFixed(1);canvas.dataset.rayMapBuilds=String(mapBuilds);canvas.dataset.renderSize=uniforms.resolution.value.toArray().join('x');statsStart=now;frames=0;}
});
