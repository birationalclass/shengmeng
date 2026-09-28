import {pointerPose} from './galaxy-balance.mjs?v=balance-2';
import {planetMotion,starMotion,stableRandom,orbitalOffset,systemStarOrbits,planetOrbitRadius} from './celestial-motion.mjs?v=nebula-63';
import {galaxyBlackHole} from './galaxy-black-hole.mjs?v=nebula-63';
import {detailedStar} from './stellar-render.mjs?v=halo-52';
import {detailedPlanet} from './planet-render.mjs?v=axial-51';
import {groups} from './model.mjs?v=nebula-63';
import {celestialLayout,bodyScale} from './celestial-rank.mjs?v=plane-size-47';
import * as T from '../../../visuals/3d/vendor/three.module.js';
import {dustField,addInflow,addNebula} from './galaxy-dust.mjs?v=nebula-63';
import {GALAXIES} from './galaxy-campaign.mjs?v=nebula-63';
export class GalaxyScene{
 constructor(canvas,onSelect,onEnter){
  this.canvas=canvas;this.onEnter=onEnter;this.onSelect=onSelect;this.selected=0;this.unlocked=0;this.completed=0;this.motion=true;this.pointer=new T.Vector2();this.balanceTarget=new T.Vector2();this.balance=new T.Vector2();this.mouseBalance=new T.Vector2();this.mouseView=false;this.spinRotation=new T.Quaternion();this.spinAxis=new T.Vector3(0,1,0);this.target=new T.Vector3();this.look=new T.Vector3();this.camera=new T.PerspectiveCamera(46,1,.1,1600);this.camera.position.set(0,9,27);this.scene=new T.Scene();this.renderer=new T.WebGLRenderer({canvas,antialias:true,alpha:true,powerPreference:'high-performance'});this.renderer.setPixelRatio(Math.min(devicePixelRatio,1.7));this.renderer.outputColorSpace=T.SRGBColorSpace;this.scene.add(new T.AmbientLight(0xb7b4ff,.6));const light=new T.DirectionalLight(0xdaf6ff,2.4);light.position.set(-8,14,12);this.scene.add(light);const pink=new T.PointLight(0xee55cc,90,50);pink.position.set(6,3,8);this.scene.add(pink);this.ray=new T.Raycaster();this.ray.layers.enable(1);this.ray.layers.enable(2);this.ray.params.Points.threshold=.5;
  this.nebula();this.stars();this.systems=GALAXIES.map((g,i)=>this.galaxy(g,i));this.planets=this.systems.flatMap(g=>g.userData.planets);
  this.measure=()=>{const b=canvas.getBoundingClientRect();this.w=b.width;this.h=b.height;this.camera.aspect=this.w/Math.max(1,this.h);this.camera.updateProjectionMatrix();this.renderer.setSize(this.w,this.h,false);};new ResizeObserver(this.measure).observe(canvas);this.measure();let start;
  canvas.addEventListener('pointerdown',e=>{start={x:e.clientX,y:e.clientY};});canvas.addEventListener('pointermove',e=>{this.pointer.set((e.clientX/this.w-.5)*2,(e.clientY/this.h-.5)*2);const b=canvas.getBoundingClientRect();this.ray.setFromCamera(new T.Vector2((e.clientX-b.left)/b.width*2-1,1-(e.clientY-b.top)/b.height*2),this.camera);const hit=this.ray.intersectObjects(this.planets.filter(p=>p.parent.visible&&Math.abs(p.userData.galaxy-this.selected)<=1),false)[0];if(hit){const d=hit.object.userData,en=document.documentElement.lang==='en';canvas.title=d.label+' · '+(en?'order ':'阶 ')+d.order+' · '+(en?d.rank.en:d.rank.zh)+' · '+(en?'conjugacy class ':'共轭类 ')+(d.classIndex+1)+' / '+d.classSize;}else canvas.title='';canvas.style.cursor=hit||this.centralHit(e.clientX,e.clientY)?'pointer':'default';});canvas.addEventListener('pointerup',e=>{if(!start)return;const dx=e.clientX-start.x,dy=e.clientY-start.y;if(this.challenge){if(Math.hypot(dx,dy)>12)return;if(this.blackHoleHit(e.clientX,e.clientY)){this.challenge.start();return;}const b=canvas.getBoundingClientRect();this.ray.setFromCamera(new T.Vector2((e.clientX-b.left)/b.width*2-1,1-(e.clientY-b.top)/b.height*2),this.camera);const hit=this.ray.intersectObjects(this.systems[this.selected].userData.planets,false)[0];if(hit)this.challenge.pick(hit.object.userData.element);return;}if(Math.abs(dx)>45&&Math.abs(dx)>Math.abs(dy)){this.onSelect(Math.max(0,Math.min(GALAXIES.length-1,this.selected+(dx<0?1:-1))));return;}if(Math.hypot(dx,dy)>12)return;const b=canvas.getBoundingClientRect();this.ray.setFromCamera(new T.Vector2((e.clientX-b.left)/b.width*2-1,1-(e.clientY-b.top)/b.height*2),this.camera);const hit=this.ray.intersectObjects(this.planets.filter(p=>p.parent.visible&&Math.abs(p.userData.galaxy-this.selected)<=1),false)[0];if(hit){if(hit.object.userData.galaxy===this.selected)this.onEnter?.();else this.onSelect(hit.object.userData.galaxy);}else if(this.centralHit(e.clientX,e.clientY))this.onEnter?.();});
  window.addEventListener('pointermove',e=>{if(e.pointerType!=='mouse'||this.challenge)return;const b=canvas.getBoundingClientRect(),pose=pointerPose(2*(e.clientX-b.left)/b.width-1,2*(e.clientY-b.top)/b.height-1);this.mouseBalance.set(pose.x,pose.z);this.mouseView=true;},{passive:true});
  window.addEventListener('pointerout',e=>{if(!e.relatedTarget)this.mouseBalance.set(0,0);});window.addEventListener('blur',()=>this.mouseBalance.set(0,0));
  this.last=performance.now();this.time=0;this.orbitTime=0;this.sceneRate=1;this.blackHoleRate=1;this.blackHoleTime=0;const frame=now=>{requestAnimationFrame(frame);const dt=Math.min(.04,(now-this.last)/1000);this.last=now;if(document.hidden||this.paused)return;this.sceneRate+=((this.challenge?.1:1)-this.sceneRate)*(1-Math.exp(-dt*1.7));this.blackHoleRate+=((this.challenge?.selecting?.1:1)-this.blackHoleRate)*(1-Math.exp(-dt*1.7));this.time+=dt*this.sceneRate*(this.motion?1:0);this.blackHoleTime+=dt*this.blackHoleRate*(this.motion?1:0);this.draw(dt);};requestAnimationFrame(frame);
 }
 nebula(){const material=new T.ShaderMaterial({side:T.BackSide,depthWrite:false,uniforms:{time:{value:0}},vertexShader:`varying vec3 v;void main(){v=position;gl_Position=projectionMatrix*modelViewMatrix*vec4(position,1.);}`,fragmentShader:`varying vec3 v;uniform float time;float hash(vec3 p){return fract(sin(dot(p,vec3(127.1,311.7,74.7)))*43758.5453);}float noise(vec3 p){vec3 i=floor(p),f=fract(p);f=f*f*(3.-2.*f);return mix(mix(mix(hash(i),hash(i+vec3(1,0,0)),f.x),mix(hash(i+vec3(0,1,0)),hash(i+vec3(1,1,0)),f.x),f.y),mix(mix(hash(i+vec3(0,0,1)),hash(i+vec3(1,0,1)),f.x),mix(hash(i+vec3(0,1,1)),hash(i+vec3(1,1,1)),f.x),f.y),f.z);}float fbm(vec3 p){float a=.5,n=0.;for(int i=0;i<5;i++){n+=a*noise(p);p=p*2.03+17.3;a*=.5;}return n;}void main(){vec3 p=normalize(v);float n=fbm(p*4.+vec3(time*.007,0,0));float f=fbm(p*8.+n*3.);float belt=exp(-pow((p.y+.13+p.x*.18)*3.8,2.));vec3 c=vec3(.006,.009,.028);c+=mix(vec3(.09,.018,.18),vec3(.008,.15,.21),smoothstep(-.3,.5,p.x))*pow(n*1.45,3.)*belt;c+=vec3(.21,.025,.12)*pow(f,4.)*belt;c*=.7+noise(p*90.)*.3;gl_FragColor=vec4(c*2.3,1.);}`});this.sky=new T.Mesh(new T.SphereGeometry(650,32,20),material);this.scene.add(this.sky);}
 points(pos,colors,size,opacity=1){const geo=new T.BufferGeometry();geo.setAttribute('position',new T.Float32BufferAttribute(pos,3));geo.setAttribute('color',new T.Float32BufferAttribute(colors,3));const mat=new T.ShaderMaterial({vertexColors:true,transparent:true,depthWrite:false,blending:T.AdditiveBlending,uniforms:{size:{value:size},opacity:{value:opacity}},vertexShader:`uniform float size;varying vec3 c;void main(){c=color;vec4 p=modelViewMatrix*vec4(position,1.);gl_PointSize=clamp(size*150.*length(modelMatrix[0].xyz)/max(1.,-p.z),.65,45.);gl_Position=projectionMatrix*p;}`,fragmentShader:`uniform float opacity;varying vec3 c;void main(){float d=length(gl_PointCoord-.5)*2.;if(d>1.)discard;float a=pow(1.-d,2.5);gl_FragColor=vec4(c,a*opacity);}`});return new T.Points(geo,mat);}
 stars(){const p=[],c=[];let seed=37;const rand=()=>{seed=(seed*16807)%2147483647;return(seed-1)/2147483646;};for(let i=0;i<4500;i++){p.push((rand()-.5)*650,(rand()-.5)*420,(rand()-.5)*600);const s=.4+rand()*.6;c.push(s*.8,s*.87,s);}this.scene.add(this.points(p,c,1.4));}
 galaxy(g,index){
  const root=new T.Group();root.position.set(index*34,Math.sin(index*1.5)*2,-index*4);root.rotation.set(.12+index*.012,0,-.3+index*.045);root.userData.planets=[];this.scene.add(root);
  const sphere=new T.SphereGeometry(1,48,32),group=groups[g.key],layout=celestialLayout(group,71+index*19),stars=layout.filter(e=>e.rank.type.endsWith('star')),starOrbits=systemStarOrbits(layout,bodyScale(g.order),71+index*131,index);
  for(let i=0;i<g.order;i++){
   const entry=layout[i],{order,rank}=entry,motion=rank.type.endsWith('planet')?planetMotion(rank.type,i+index*131,entry.slot,entry.host+index*131):(rank.type.endsWith('star')?starOrbits[stars.findIndex(e=>e.element===i)]:starMotion(i+index*131)),kind=rank.type==='ring-planet'?3:rank.type==='gas-planet'?1:rank.type==='ice-planet'?2:0;
   const radius=1.5*bodyScale(g.order)*rank.scale*(rank.type.endsWith('planet')?1:2);
   const planet=rank.type.endsWith('planet')?detailedPlanet(sphere,kind,entry.appearanceSeed+index*13):(order===1?galaxyBlackHole(sphere):detailedStar(sphere,rank,entry.appearanceSeed+index*13));
   planet.scale.setScalar(radius);planet.userData.baseSize=radius;planet.userData.light={value:1};planet.userData.bodyOpacity={value:1};planet.traverse(o=>{if(!o.material?.isShaderMaterial)return;o.material.uniforms.bodyLight=planet.userData.light;o.material.uniforms.bodyOpacity=planet.userData.bodyOpacity;o.material.transparent=true;o.material.fragmentShader="uniform float bodyLight;uniform float bodyOpacity;\n"+o.material.fragmentShader.replace(/}\s*$/, "gl_FragColor.rgb*=bodyLight;gl_FragColor.a*=bodyOpacity; if(bodyOpacity<.003)discard;\n}");});
   if((kind===0||kind===3)&&rank.type.endsWith('planet')){const ringTilt=(kind===0?23.44:10+20*stableRandom(i*47+index*83))*Math.PI/180;const orbitFrame=new T.Quaternion().setFromAxisAngle(new T.Vector3(0,1,0),motion.node).multiply(new T.Quaternion().setFromAxisAngle(new T.Vector3(1,0,0),-motion.inclination));planet.userData.spinBasePlanet=orbitFrame.multiply(new T.Quaternion().setFromAxisAngle(new T.Vector3(0,1,0),stableRandom(i*67+index)*Math.PI*2)).multiply(new T.Quaternion().setFromAxisAngle(new T.Vector3(1,0,0),ringTilt));planet.quaternion.copy(planet.userData.spinBasePlanet);}

   if(order===1)planet.position.set(0,0,0);
   else if(rank.type.endsWith('star'))planet.position.set(Math.cos(motion.phase)*motion.radius,0,Math.sin(motion.phase)*motion.radius);
   planet.userData={...planet.userData,...entry,motion,galaxy:index,label:group.labels[i]};if(rank.type.endsWith('star'))planet.userData.spinBase=new T.Quaternion().setFromEuler(new T.Euler(motion.spinTilt,motion.spinNode,0,'YXZ'));planet.traverse(part=>part.layers.set(1));root.add(planet);root.userData.planets.push(planet);

  }
  let orbitExtent=0;
  for(const p of root.userData.planets){const d=p.userData;if(d.rank.type.endsWith('star'))orbitExtent=Math.max(orbitExtent,d.motion.radius+p.scale.x);if(d.host!==null){const host=root.userData.planets[d.host],r=planetOrbitRadius(host.scale.x,p.scale.x,d.element,d.galaxy,d.slot);orbitExtent=Math.max(orbitExtent,host.userData.motion.radius+r+p.scale.x*(d.rank.type==='ring-planet'?2.25:1.055));}}
  const innerDust=8.5*1.35/2*bodyScale(g.order)*3,outerDust=orbitExtent*1.12;
  const field=dustField(g.key,matchMedia('(max-width:700px)').matches?15000:24000,innerDust,outerDust),dust=this.points(field.positions,field.colors,.78,.7);root.add(dust);root.userData.dust=dust;root.userData.cloud=addNebula(T,root,g.key,innerDust,outerDust);
  root.userData.inflow=addInflow(T,root,field,innerDust,outerDust,matchMedia('(max-width:700px)').matches?140:220);

  root.userData.orbitExtent=orbitExtent*1.06;
  // Keep body framing independent of the expanded decorative/orbit envelope.
  // Otherwise extending outer orbits silently zooms every celestial model away.
  const framingInner=2.5*(8.5*1.35/2)*bodyScale(g.order)*2+bodyScale(g.order)*1.6;
  root.userData.extent=Math.max(11.5,framingInner+7.4+bodyScale(g.order)*6);
  const completion={value:0};root.userData.completion=completion;
  root.traverse(part=>{const material=part.material;if(!material?.isShaderMaterial)return;material.uniforms.completionColor=completion;material.fragmentShader='uniform float completionColor;\n'+material.fragmentShader.replace(/}\s*$/, 'float gray=dot(gl_FragColor.rgb,vec3(.2126,.7152,.0722));gl_FragColor.rgb=mix(vec3(gray),gl_FragColor.rgb,completionColor);\n}');});
  return root;
 }
 blackHoleHit(x,y){const b=this.canvas.getBoundingClientRect(),hole=this.systems[this.selected].userData.planets.find(p=>p.userData.order===1),center=hole.getWorldPosition(new T.Vector3()),projected=center.clone().project(this.camera),scale=hole.getWorldScale(new T.Vector3()).x,d=this.camera.position.distanceTo(center),radius=5.7375*scale*b.height/(2*d*Math.tan(23*Math.PI/180));return Math.hypot(x-b.left-(projected.x+1)*b.width/2,y-b.top-(1-projected.y)*b.height/2)<=radius;}
 centralHit(x,y){const b=this.canvas.getBoundingClientRect(),s=this.systems[this.selected],center=s.position.clone().project(this.camera),distance=this.camera.position.distanceTo(s.position),r=s.scale.x*9*b.height/(2*distance*Math.tan(23*Math.PI/180));return Math.pow((x-b.left-(center.x+1)*b.width/2)/r,2)+Math.pow((y-b.top-(1-center.y)*b.height/2)/(r*.65),2)<1;}
 select(index){if(!Number.isInteger(index)||!this.systems[index])return;this.selected=index;}
 draw(dt){
 this.challenge?.tick(dt);if(this.motion)this.orbitTime+=dt*this.sceneRate;
 const narrow=this.w<700,aspect=this.camera.aspect;
 this.balance.lerp(this.motion?(this.mouseView?this.mouseBalance:this.balanceTarget):new T.Vector2(),1-Math.exp(-dt*5));
 this.camera.position.set(0,12,27);this.camera.lookAt(0,0,0);this.camera.updateMatrixWorld(true);
 const depth=this.camera.position.length(),halfH=depth*Math.tan(23*Math.PI/180),halfW=halfH*aspect;
 const right=new T.Vector3(1,0,0).applyQuaternion(this.camera.quaternion),up=new T.Vector3(0,1,0).applyQuaternion(this.camera.quaternion);
 const selectedSystem=this.systems[this.selected];
 const extent=this.challenge?selectedSystem.userData.orbitExtent:selectedSystem.userData.extent;
 const mainScale=Math.min(1,halfW*(this.challenge?(narrow?.58:.72):narrow?.69:.57)/extent,halfH*(this.challenge?.51:.65)/(extent*.78));
 this.systems.forEach((s,i)=>{
  const delta=i-this.selected,near=Math.abs(delta)<=1&&!this.challenge||delta===0;
  if(!near&&!s.userData.layoutReady){s.visible=false;return;}
  const x=delta===0?0:Math.sign(delta)*(near?.82:1.7);
  const y=delta===0?0:(narrow?-.37:-.72);
  const position=right.clone().multiplyScalar(x*halfW).addScaledVector(up,y*halfH);
  const scale=mainScale*(delta===0?1:near?.24:.12),ease=1-Math.exp(-dt*3.1);
  // New neighbors start beyond the viewport; outgoing neighbors remain visible until offscreen.
  if(near&&(!s.visible||!s.userData.layoutReady)){
   s.position.copy(delta===0?position:right.clone().multiplyScalar(Math.sign(delta)*1.7*halfW).addScaledVector(up,y*halfH));
   s.scale.setScalar(delta===0?scale:mainScale*.12);s.userData.layoutReady=true;s.visible=true;
  }
  s.position.lerp(position,ease);s.scale.lerp(new T.Vector3(scale,scale,scale),ease);
  if(!near&&s.position.distanceTo(position)<.03)s.visible=false;
 });

 this.sky.position.copy(this.camera.position);this.sky.material.uniforms.time.value=this.time;this.systems.forEach((s,i)=>{s.userData.viewWeight=(s.userData.viewWeight??0)+((i===this.selected?1:0)-(s.userData.viewWeight??0))*(1-Math.exp(-dt*5));s.rotation.x=.12+i*.012+this.balance.x*s.userData.viewWeight;s.rotation.z=-.3+i*.045+this.balance.y*s.userData.viewWeight;s.rotation.y=-this.orbitTime*.045;s.userData.completion.value+=((this.colors?.[i]??(i<this.completed?1:0))-s.userData.completion.value)*(1-Math.exp(-dt*1.7));s.userData.inflow.material.uniforms.time.value=this.time;s.userData.dust.rotation.y=-this.time*.018;s.userData.inflow.rotation.y=s.userData.dust.rotation.y;s.userData.cloud.rotation.y=s.userData.dust.rotation.y;s.userData.cloud.material.uniforms.opacity.value=.25+.55*s.userData.completion.value;s.userData.dust.material.uniforms.opacity.value=.38+.32*s.userData.completion.value;s.userData.inflow.material.uniforms.opacity.value=.3+.32*s.userData.completion.value;s.userData.planets.forEach(p=>{if(p.userData.spinBase)p.quaternion.copy(p.userData.spinBase).multiply(this.spinRotation.setFromAxisAngle(this.spinAxis,p.userData.motion.spinPhase-this.time*.15));else if(p.userData.order!==1){if(p.userData.spinBasePlanet)p.quaternion.copy(p.userData.spinBasePlanet).multiply(this.spinRotation.setFromAxisAngle(this.spinAxis,-this.time*p.userData.motion.spin));else p.rotation.y=-this.time*p.userData.motion.spin;}else p.rotation.y=-s.rotation.y;if(p.material.uniforms?.time)p.material.uniforms.time.value=this.time;if(p.userData.effects)p.userData.effects.forEach(m=>m.uniforms.time.value=p.userData.order===1?this.blackHoleTime:this.time);});}); this.systems.forEach(s=>{if(!s.visible)return;
  // Move all hosts first, so each planet follows its host in the same frame.
  for(const p of s.userData.planets){const d=p.userData;if(!d.rank.type.endsWith('star'))continue;const a=d.motion.phase+this.orbitTime*d.motion.orbit,r=d.motion.radius;p.position.set(Math.cos(a)*r,0,Math.sin(a)*r);}
  for(const p of s.userData.planets){const d=p.userData;if(d.host===null)continue;const host=s.userData.planets[d.host],r=planetOrbitRadius(host.userData.baseSize,p.userData.baseSize,d.element,d.galaxy,d.slot),a=d.phase+this.orbitTime*d.motion.orbit;const offset=orbitalOffset(d.motion,a,r);p.position.copy(host.position).add(new T.Vector3(offset.x,offset.y,offset.z));}
  });
 this.challenge?.pose();
 // Keep the shared accretion/stellar plane in the approved low, oblique view range.
 for(const s of this.systems){if(!s.visible)continue;const view=this.camera.position.clone().sub(s.position).normalize(),normal=new T.Vector3(0,1,0).applyQuaternion(s.quaternion),dot=normal.dot(view),elevation=Math.asin(Math.min(1,Math.max(-1,dot))),target=Math.max(3*Math.PI/180,Math.min(20*Math.PI/180,elevation));if(Math.abs(target-elevation)>1e-6){const tangent=normal.clone().addScaledVector(view,-dot).normalize(),desired=tangent.multiplyScalar(Math.cos(target)).addScaledVector(view,Math.sin(target));s.quaternion.premultiply(new T.Quaternion().setFromUnitVectors(normal,desired));}}
 this.scene.updateMatrixWorld(true);this.camera.updateMatrixWorld(true);this.challenge?.project();
 this.systems.forEach(s=>{if(!s.visible)return;for(const p of s.userData.planets){if(p.userData.hostLight)s.userData.planets[p.userData.host].getWorldPosition(p.userData.hostLight.value);}});
 this.systems.forEach((s,i)=>{if(!s.visible)return;s.userData.planets.forEach(p=>p.userData.updateBlackHole?.(this.renderer,this.camera));});this.camera.layers.set(0);this.renderer.render(this.scene,this.camera);this.renderer.autoClear=false;this.renderer.clearDepth();this.camera.layers.set(1);this.renderer.render(this.scene,this.camera);this.camera.layers.set(0);this.renderer.autoClear=true;}
}
