import * as THREE from '../3d/vendor/three.module.js';
import {OrbitControls} from '../3d/vendor/OrbitControls.js';
import {EllipticRenderer} from './elliptic-renderer.js';
import {ringPoint,branchPoint,bedHeight,tideLevel} from './elliptic-model.js';
import {motion,distanceSampler} from './beach-navigation.js';

const $=id=>document.getElementById(id),canvas=$('beach');
const state={view:'person',angle:0,yaw:0,pitch:-.095,wave:.6,tide:2.55,tidal:true,sun:24,time:7.1,paused:matchMedia('(prefers-reduced-motion: reduce)').matches};
let active=true,engine,controls,last=0,lastPaint=0,frames=0,measure=0,drag=null,dirty=true;
let sampleDistance,baseYaw=0,eyeHeight=1.7,heldButton=null;
const walkPosition=new THREE.Vector2(),keys=new Set();
const labels={wash:'漫滩近看 · 涨潮时浅水掠过沙脊',person:'环形沙带 · 向圈内望去',outer:'环形沙带 · 望向外海',branch:'右侧沙带 · 远端渐入海中',aerial:'空中俯瞰 · 仅曲线路径为沙滩',plan:'等比例俯视 · 辅助网格每格 0.25 km'};
const isHuman=()=>['person','outer','branch','wash'].includes(state.view);
const planHeight=()=>Math.max(3300,1650/(Math.tan(24*Math.PI/180)*engine.camera.aspect));
function placePerson(reset=false){
 if(!isHuman())return;
 if(reset){
 let p,n;
 if(state.view==='branch'){p=[2000,0];n=[-1,0];}
 else{
  const t=state.angle*Math.PI/180;p=ringPoint(t);
  const a=ringPoint(t-.001),b=ringPoint(t+.001),length=Math.hypot(b[0]-a[0],b[1]-a[1]);
  n=[-(b[1]-a[1])/length,(b[0]-a[0])/length];
  if(state.view==='outer')n=n.map(v=>-v);
 }
 // Start four metres from the water, so the near shoreline is visible.
 const offset=state.view==='wash'?0:46;
 walkPosition.set(p[0]+n[0]*offset,p[1]+n[1]*offset);baseYaw=Math.atan2(n[1],n[0])+(state.view==='wash'?Math.PI/2:0);eyeHeight=1.7;
 }
 const ground=Math.max(tideLevel(state)-.35,bedHeight(sampleDistance(walkPosition.x,walkPosition.y),walkPosition.x,walkPosition.y));
 engine.camera.position.set(walkPosition.x,ground+eyeHeight,walkPosition.y);
 const near=Math.max(.15,eyeHeight*.003);
 if(engine.camera.near!==near){engine.camera.near=near;engine.camera.updateProjectionMatrix();}
 const yaw=baseYaw+state.yaw,cp=Math.cos(state.pitch);
 engine.camera.lookAt(engine.camera.position.clone().add(new THREE.Vector3(Math.cos(yaw)*cp,Math.sin(state.pitch),Math.sin(yaw)*cp)));
 $('position').textContent=`x ${(walkPosition.x/1000).toFixed(3)} · y ${(-walkPosition.y/1000).toFixed(3)} km · 高 ${eyeHeight.toFixed(1)} m`;
 canvas.dataset.position=[walkPosition.x,engine.camera.position.y,walkPosition.y].map(v=>v.toFixed(3)).join(',');
 canvas.dataset.look=[yaw,state.pitch].map(v=>v.toFixed(3)).join(',');
}
function move(forward,right,up,metres){
 if(!isHuman())return;
 const delta=motion(baseYaw+state.yaw,forward,right,up,metres);
 walkPosition.x+=delta.x;walkPosition.y+=delta.z;eyeHeight=Math.max(1.7,Math.min(5000,eyeHeight+delta.height));
 placePerson();dirty=true;
}
const actions={forward:[1,0,0],back:[-1,0,0],left:[0,-1,0],right:[0,1,0],up:[0,0,1],down:[0,0,-1]};
function clearMovement(){keys.clear();heldButton=null;drag=null;}
function navigate(dt,now){
 if(!isHuman())return;
 let f=Number(keys.has('KeyW')||keys.has('ArrowUp'))-Number(keys.has('KeyS')||keys.has('ArrowDown'));
 let r=Number(keys.has('KeyD')||keys.has('ArrowRight'))-Number(keys.has('KeyA')||keys.has('ArrowLeft'));
 let u=Number(keys.has('KeyE'))-Number(keys.has('KeyQ'));
 if(heldButton&&now-heldButton.start>250){const v=actions[heldButton.action];f+=v[0];r+=v[1];u+=v[2];}
 if(f||r||u)move(f,r,u,dt*(keys.has('ShiftLeft')||keys.has('ShiftRight')?75:18));
}
function selectView(view){
 state.view=view;state.yaw=0;state.pitch=view==='wash'?-.3:-.095;clearMovement();
 controls.enabled=!isHuman();controls.enableRotate=view!=='plan';controls.enablePan=true;
 engine.camera.fov=isHuman()?64:48;engine.camera.up.set(0,1,0);
 engine.camera.near=isHuman()?.15:10;
 if(view==='aerial'){engine.camera.position.set(-1000,2300,1900);controls.target.set(1000,0,0);controls.update();}
 else if(view==='plan'){engine.camera.up.set(0,0,-1);engine.camera.position.set(1150,planHeight(),0);controls.target.set(1150,0,0);controls.update();}
 else placePerson(true);
 engine.camera.updateProjectionMatrix();
 document.querySelectorAll('[data-view]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.view===view)));
 $('walkLabel').hidden=!['person','outer','wash'].includes(view);$('viewLabel').textContent=labels[view];
 document.querySelector('.map-heading span').textContent=isHuman()?'你在这里':'地形总览';
 $('navigation').hidden=!isHuman();$('position').hidden=!isHuman();
 $('help').textContent=isHuman()?'拖动环顾 · WASD / 方向键移动 · Q 降 / E 升 · Shift 加速 · 滚轮前后移动':view==='plan'?'滚轮缩放 · 拖动平移 · 网格间距 0.25 km':'拖动旋转 · 滚轮缩放 · 右键平移';
 controls.mouseButtons.LEFT=view==='plan'?THREE.MOUSE.PAN:THREE.MOUSE.ROTATE;
 controls.touches.ONE=view==='plan'?THREE.TOUCH.PAN:THREE.TOUCH.ROTATE;
 dirty=true;
}
function drawMap(){
 const c=$('map'),ctx=c.getContext('2d'),W=c.width,H=c.height;
 ctx.clearRect(0,0,W,H);const scale=135;
 const point=p=>[44+p[0]/1000*scale,H/2+p[1]/1000*scale];
 ctx.strokeStyle='#35676b26';ctx.lineWidth=1;
 ctx.font='18px system-ui';ctx.fillStyle='#527274';
 for(let x=0;x<=3.5;x+=.5){const px=point([x*1000,0])[0];ctx.beginPath();ctx.moveTo(px,12);ctx.lineTo(px,H-24);ctx.stroke();ctx.fillText(x.toFixed(1),px-10,H-4);}
 for(let z=-1;z<=1;z+=.5){const py=point([0,z*1000])[1];ctx.beginPath();ctx.moveTo(15,py);ctx.lineTo(W,py);ctx.stroke();}
 for(const [fn,start,end] of [[ringPoint,0,Math.PI*2],[branchPoint,-1.3,1.3]]){
  ctx.beginPath();for(let i=0;i<=400;i++){const p=point(fn(start+(end-start)*i/400));i?ctx.lineTo(...p):ctx.moveTo(...p);}
  ctx.strokeStyle='#cfbd8d';ctx.lineWidth=13.5;ctx.stroke();ctx.strokeStyle='#947f53';ctx.lineWidth=1;ctx.stroke();
 }
 if(engine){
  const cam=engine.camera,p=point([cam.position.x,cam.position.z]);
  if(isHuman()){
   const dir=cam.getWorldDirection(new THREE.Vector3()),end=[p[0]+dir.x*43,p[1]+dir.z*43];
   ctx.strokeStyle='#245b65';ctx.lineWidth=4;ctx.beginPath();ctx.moveTo(...p);ctx.lineTo(...end);ctx.stroke();
   const a=Math.atan2(dir.z,dir.x);ctx.beginPath();ctx.moveTo(...end);ctx.lineTo(end[0]-13*Math.cos(a-.5),end[1]-13*Math.sin(a-.5));ctx.lineTo(end[0]-13*Math.cos(a+.5),end[1]-13*Math.sin(a+.5));ctx.closePath();ctx.fillStyle='#245b65';ctx.fill();
   ctx.beginPath();ctx.arc(...p,7,0,Math.PI*2);ctx.fill();
  }
 }
}
function resize(){
 const ratio=Math.min(devicePixelRatio,Math.sqrt(1000000/(innerWidth*innerHeight)));
 engine.resize(Math.round(innerWidth*ratio),Math.round(innerHeight*ratio));
 if(state.view==='plan'){engine.camera.position.set(controls.target.x,planHeight(),controls.target.z);controls.update();}
 dirty=true;
}
function pauseLabel(){ $('pause').textContent=state.paused?'继续海浪':'暂停海浪';$('pause').setAttribute('aria-pressed',String(state.paused));}
function frame(now){
 requestAnimationFrame(frame);
 if(!active||document.hidden){last=0;clearMovement();return;}
 if(now-lastPaint<32)return;lastPaint=now;
 const dt=last?Math.min(.1,(now-last)/1000):0;last=now;
 navigate(dt,now);
 if(!state.paused){state.time+=dt;dirty=true;if(state.tidal)placePerson();}
 const tide=tideLevel(state);$('tideNow').textContent=`当前 ${tide.toFixed(2)} m · ${tide>2.74?'浅水漫过沙脊':tide>2.54?'沙脊局部漫水':'沙脊露出'} · 远端渐入海中`;
 canvas.dataset.tide=tide.toFixed(3);
 if(controls.enabled){const before=engine.camera.position.clone();controls.update();if(before.distanceToSquared(engine.camera.position)>.00001)dirty=true;}
 if(dirty){engine.draw(state);drawMap();canvas.dataset.time=state.time.toFixed(3);canvas.dataset.view=state.view;dirty=false;frames++;}
 if(now-measure>2000){$('status').textContent=state.paused?'已暂停 · 02 新水材质':`${Math.round(frames*1000/(now-measure))} 帧/秒 · 02 新水材质`;measure=now;frames=0;}
}
try{
 const field=await new THREE.TextureLoader().loadAsync('./elliptic-distance.png');
 field.flipY=false;field.colorSpace=THREE.NoColorSpace;field.minFilter=field.magFilter=THREE.LinearFilter;field.generateMipmaps=false;
 sampleDistance=distanceSampler(field.image);
 engine=new EllipticRenderer(canvas,field);controls=new OrbitControls(engine.camera,canvas);controls.enableDamping=true;controls.minDistance=350;controls.maxDistance=14000;controls.maxPolarAngle=Math.PI*.48;
 controls.addEventListener('change',()=>dirty=true);selectView('wash');resize();pauseLabel();
 new ResizeObserver(()=>document.documentElement.style.setProperty('--control-height',document.querySelector('.controls').offsetHeight+'px')).observe(document.querySelector('.controls'));
 document.querySelectorAll('[data-view]').forEach(b=>b.onclick=()=>selectView(b.dataset.view));
 $('walk').oninput=e=>{state.angle=+e.target.value;$('walkValue').textContent=state.angle+'°';placePerson(true);dirty=true;};
 $('light').onchange=e=>{state.sun=+e.target.value;dirty=true;};
 $('tide').oninput=e=>{state.tide=+e.target.value;$('tideValue').textContent=state.tide.toFixed(2)+' m';placePerson();dirty=true;};
 $('tidal').onclick=()=>{state.tidal=!state.tidal;$('tidal').setAttribute('aria-pressed',String(state.tidal));$('tidal').textContent=state.tidal?'潮汐起落：开':'潮汐起落：关';placePerson();dirty=true;};
 $('wave').oninput=e=>{state.wave=+e.target.value;$('waveValue').textContent=state.wave.toFixed(1)+' m';dirty=true;};
 $('pause').onclick=()=>{state.paused=!state.paused;pauseLabel();last=0;dirty=true;};
 $('reset').onclick=()=>{state.angle=0;$('walk').value=0;$('walkValue').textContent='0°';selectView(state.view);};
 canvas.addEventListener('pointerdown',e=>{if(!isHuman())return;canvas.focus({preventScroll:true});drag={id:e.pointerId,x:e.clientX,y:e.clientY,pan:e.button===2};canvas.setPointerCapture(e.pointerId);});
 canvas.addEventListener('pointermove',e=>{if(!drag||e.pointerId!==drag.id)return;
  const dx=e.clientX-drag.x,dy=e.clientY-drag.y;
  if(drag.pan){move(-dy,dx,0,Math.hypot(dx,dy)*.12);}
  else{state.yaw-=dx*.003;state.pitch=Math.max(-1.54,Math.min(1.54,state.pitch+dy*.003));placePerson();dirty=true;}
  drag.x=e.clientX;drag.y=e.clientY;
 });
 canvas.addEventListener('pointerup',()=>drag=null);canvas.addEventListener('pointercancel',()=>drag=null);
 canvas.addEventListener('contextmenu',e=>e.preventDefault());
 canvas.addEventListener('wheel',e=>{if(!isHuman())return;e.preventDefault();move(1,0,0,-Math.max(-150,Math.min(150,e.deltaY))*.08);},{passive:false});
 const codes=new Set(['KeyW','KeyS','KeyA','KeyD','ArrowUp','ArrowDown','ArrowLeft','ArrowRight','KeyQ','KeyE','ShiftLeft','ShiftRight']);
 addEventListener('keydown',e=>{
  if(!isHuman()||!codes.has(e.code)||e.ctrlKey||e.metaKey||e.altKey||e.target.matches('input,select,textarea'))return;
  e.preventDefault();if(!keys.has(e.code)){
   const codeAction={KeyW:'forward',ArrowUp:'forward',KeyS:'back',ArrowDown:'back',KeyA:'left',ArrowLeft:'left',KeyD:'right',ArrowRight:'right',KeyQ:'down',KeyE:'up'};
   if(codeAction[e.code])move(...actions[codeAction[e.code]],1);
  }keys.add(e.code);
 });
 addEventListener('keyup',e=>keys.delete(e.code));addEventListener('blur',clearMovement);
 document.addEventListener('visibilitychange',clearMovement);
 document.querySelectorAll('[data-move]').forEach(button=>{
  let longPress=false;
  button.onpointerdown=e=>{longPress=false;heldButton={action:button.dataset.move,start:performance.now()};button.setPointerCapture(e.pointerId);};
  button.onpointerup=()=>{longPress=!!heldButton&&performance.now()-heldButton.start>250;heldButton=null;};
  button.onpointercancel=button.onlostpointercapture=()=>{heldButton=null;};
  button.onclick=()=>{if(!longPress)move(...actions[button.dataset.move],10);longPress=false;};
 });
 addEventListener('resize',resize);
 addEventListener('message',e=>{if(e.origin===window.location.origin&&e.source===parent&&e.data?.type==='ocean-experiment-visibility'){active=!!e.data.active;clearMovement();last=0;dirty=true;}});
 canvas.addEventListener('webglcontextlost',e=>{e.preventDefault();$('error').hidden=false;$('error').textContent='图形上下文已中断，请刷新恢复场景。';active=false;});
 engine.draw(state);drawMap();$('status').textContent='02 新水材质 · 实时渲染';requestAnimationFrame(frame);
}catch(error){$('error').hidden=false;$('error').textContent='场景无法加载：'+error.message;$('status').textContent='加载失败';console.error(error);}
