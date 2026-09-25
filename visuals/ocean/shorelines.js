import * as THREE from '../3d/vendor/three.module.js';
import {OrbitControls} from '../3d/vendor/OrbitControls.js';
import {makeWaveSpectrum} from './wave-spectrum.js?v=20260925-ocean-5';
const $=id=>document.getElementById(id);
const field=`uniform float shape,tide,time,showRoute;uniform vec4 waves[32];uniform vec2 phases[32];
float hash(vec2 p){return fract(sin(dot(p,vec2(127.1,311.7)))*43758.5453);}
float noise(vec2 p){vec2 i=floor(p),f=fract(p);f=f*f*(3.-2.*f);return mix(mix(hash(i),hash(i+vec2(1,0)),f.x),mix(hash(i+vec2(0,1)),hash(i+1.),f.x),f.y);}
float capsule(vec2 p,vec2 a,vec2 b,float r){vec2 q=p-a,d=b-a;float t=clamp(dot(q,d)/dot(d,d),0.,1.);return length(q-d*t)-r;}
float shore(vec2 p){
 float d;
 if(shape<.5){d=min(capsule(p,vec2(0),vec2(-23,-18),2.8),min(capsule(p,vec2(0),vec2(22,-13),3.2),capsule(p,vec2(0),vec2(1,24),3.8)));d=min(d,min(length(p-vec2(-23,-18))-10.,min(length(p-vec2(22,-13))-8.,length(p-vec2(1,25))-11.)));}
 else if(shape<1.5){d=max(length(p)-35.,-(length(p-vec2(0,-13))-29.));}
 else{vec2 a=vec2(0,22),b=vec2(5,-29),q=p-a,v=b-a;float t=clamp(dot(q,v)/dot(v,v),0.,1.);d=min(length(q-v*t)-(1.+13.*pow(1.-t,1.6)),length(p-vec2(0,29))-19.);}
 return d+(noise(p*.25)-.5)*.65;
}
float terrain(vec2 p){float d=shore(p);float h=.35-d*.15;
 float hills=0.;
 if(shape<.5){hills=8.*exp(-dot(p-vec2(-23,-18),p-vec2(-23,-18))/48.)+5.*exp(-dot(p-vec2(22,-13),p-vec2(22,-13))/25.)+11.*exp(-dot(p-vec2(1,27),p-vec2(1,27))/49.);}
 else if(shape<1.5){hills=6.*(1.-smoothstep(-9.,-3.,d))*(.7+.3*sin(p.x*.23));}
 else hills=4.*exp(-dot(p-vec2(0,32),p-vec2(0,32))/130.);
 return h+hills*(.85+.15*noise(p*.65));
}
float surface(vec2 p){float d=shore(p);float swell=0.;for(int i=0;i<32;i++){vec4 w=waves[i];swell+=w.w*sin(dot(p,w.xy)*w.z-time*phases[i].x+phases[i].y);}
 float depth=max(0.,tide-terrain(p));float breaker=pow(.5+.5*sin(d*.88+time*1.25+noise(p*.14)),5.)*.17*exp(-depth*.28);
 return tide+swell*.35*smoothstep(0.,2.,depth)+breaker;}
`;
try{
const renderer=new THREE.WebGLRenderer({canvas:$('coast'),antialias:true});renderer.setPixelRatio(Math.min(devicePixelRatio,1.7));renderer.outputColorSpace=THREE.SRGBColorSpace;renderer.toneMapping=THREE.ACESFilmicToneMapping;
const scene=new THREE.Scene();scene.background=new THREE.Color('#0a647d');const camera=new THREE.PerspectiveCamera(43,1,.1,500);camera.position.set(58,104,96);camera.lookAt(0,0,9);
const controls=new OrbitControls(camera,renderer.domElement);controls.target.set(0,0,9);controls.enableDamping=true;controls.maxPolarAngle=1.32;controls.minDistance=35;controls.maxDistance=175;
const spectrum=makeWaveSpectrum(.4),uniforms={shape:{value:0},tide:{value:0},time:{value:0},showRoute:{value:1},waves:{value:spectrum.map(w=>new THREE.Vector4(w.x,w.z,w.k,w.amplitude))},phases:{value:spectrum.map(w=>new THREE.Vector2(w.omega,w.phase))}};
const geometry=new THREE.PlaneGeometry(420,420,480,480);geometry.rotateX(-Math.PI/2);
const sand=new THREE.ShaderMaterial({uniforms,vertexShader:field+`varying vec3 vP;void main(){vP=vec3(position.x,terrain(position.xz),position.z);gl_Position=projectionMatrix*modelViewMatrix*vec4(vP,1.);}`,fragmentShader:field+`varying vec3 vP;void main(){vec2 p=vP.xz;float h=vP.y,d=shore(p),grain=noise(p*(shape>1.5?19.:110.));vec3 n=normalize(vec3(terrain(p-vec2(.05,0))-terrain(p+vec2(.05,0)),.1,terrain(p-vec2(0,.05))-terrain(p+vec2(0,.05))));vec3 sand=mix(vec3(.77,.65,.44),vec3(.62,.62,.53),step(1.5,shape));sand*=.93+grain*.14;float wet=1.-smoothstep(tide+.08,tide+.65,h);sand*=mix(1.,.63,wet);float canopy=smoothstep(1.8,3.,h)*(1.-smoothstep(-4.,-1.,d));vec3 green=mix(vec3(.035,.12,.06),vec3(.14,.25,.09),noise(p*1.5));vec3 c=mix(sand,green,canopy);c*=.55+.55*max(0.,dot(n,normalize(vec3(-.6,1.,.3))));float line=(1.-smoothstep(.06,.15,abs(h)))*showRoute;c=mix(c,vec3(1.,.78,.33),line*.9);gl_FragColor=vec4(c,1.);#include <tonemapping_fragment>
#include <colorspace_fragment>
}`.replace(';#include',';\n#include')});
scene.add(new THREE.Mesh(geometry,sand));
const water=new THREE.ShaderMaterial({uniforms,transparent:true,depthWrite:true,vertexShader:field+`varying vec3 vP;void main(){vP=vec3(position.x,surface(position.xz),position.z);gl_Position=projectionMatrix*modelViewMatrix*vec4(vP,1.);}`,fragmentShader:field+`varying vec3 vP;void main(){vec2 p=vP.xz;float depth=vP.y-terrain(p);if(depth<=0.)discard;float eps=.09;vec3 n=normalize(vec3(surface(p-vec2(eps,0))-surface(p+vec2(eps,0)),2.*eps,surface(p-vec2(0,eps))-surface(p+vec2(0,eps))));vec3 view=normalize(cameraPosition-vP);float f=.0204+.9796*pow(1.-max(0.,dot(n,view)),5.);vec3 trans=exp(-vec3(.48,.16,.09)*depth);vec3 bottom=mix(vec3(.56,.49,.32),vec3(.43,.44,.39),step(1.5,shape));bottom*=.91+.09*noise(p*70.);vec3 col=bottom*trans+vec3(.006,.075,.13)*(1.-trans);col=mix(col,vec3(.45,.69,.78),f);vec3 halfV=normalize(view+normalize(vec3(-.6,1.,.3)));col+=vec3(1.,.94,.75)*pow(max(0.,dot(n,halfV)),280.)*.6;float d=shore(p);float front=pow(.5+.5*sin(d*.88+time*1.25+noise(p*.14)),16.);float foam=front*exp(-depth*.65)*smoothstep(.02,.2,depth);foam=max(foam,exp(-pow((depth-.06)/.08,2.))*.65);foam*=smoothstep(.2,.8,noise(p*5.+time*.15));col=mix(col,vec3(.87,.95,.90),foam*.86);float contour=1.-smoothstep(.025,.065,abs(fract(depth*.5)-.5));col=mix(col,vec3(.33,.81,.79),contour*showRoute*.05*exp(-depth*.3));gl_FragColor=vec4(col,smoothstep(0.,.05,depth));
#include <tonemapping_fragment>
#include <colorspace_fragment>
}`});scene.add(new THREE.Mesh(geometry,water));
const names=['三岛之间','月牙拥海','迎向海流'];const intros=['三座岛屿，由浅水中的人字形沙洲连接。潮位升高时，沙洲逐渐变窄。','内凹弧形海湾，两侧岬角围合出一片浅水。沿着月牙形岸线观察冲刷带。','尖岬伸入海中，两侧均有浪线。这里使用灰金色砾石，而非细白沙。'];
const materials=['浅色细沙 · 三岛沙洲','暖色细沙 · 内凹海湾','灰金砾石 · 双侧冲刷'];const sources=[['泰国南园岛','https://visitkohtao.org/detail-sub/3/22/48/koh-nang-yuan'],['玛雅湾弧形海滩','https://www.tourismthailand.org/Destinations/Provinces/Bangkok/359'],['克罗地亚金角湾','https://www.visit-croatia.hr/en/destinations/central-dalmatia/island-brac/zlatni-rat']];
const states=[{tide:0,time:0},{tide:0,time:0},{tide:0,time:0}];let selected=0,paused=false,active=true,last=0,top=false;
document.querySelectorAll('[data-shape]').forEach(b=>b.onclick=()=>{selected=Number(b.dataset.shape);uniforms.shape.value=selected;uniforms.tide.value=states[selected].tide;$('tide').value=states[selected].tide;$('level').textContent=states[selected].tide.toFixed(2)+' m';$('title').textContent=names[selected];$('intro').textContent=intros[selected];$('material').textContent=materials[selected];$('source').href=sources[selected][1];$('source').textContent='参考：'+sources[selected][0]+' ↗';document.querySelectorAll('[data-shape]').forEach(q=>q.setAttribute('aria-pressed',String(q===b)));});
$('tide').oninput=e=>{states[selected].tide=uniforms.tide.value=Number(e.target.value);$('level').textContent=uniforms.tide.value.toFixed(2)+' m';};$('route').onchange=e=>uniforms.showRoute.value=Number(e.target.checked);$('pause').onclick=()=>{paused=!paused;$('pause').textContent=paused?'继续海浪':'暂停海浪';};$('view').onclick=()=>{top=!top;camera.position.set(top?0:68,top?125:90,top?.01:89);controls.target.set(0,0,0);controls.update();$('view').textContent=top?'返回斜视':'俯视路线';};
function resize(){const h=Math.max(220,innerHeight-190);renderer.setSize(innerWidth,h,false);camera.aspect=innerWidth/h;camera.updateProjectionMatrix();}addEventListener('resize',resize);resize();
addEventListener('message',e=>{if(e.origin===location.origin&&e.source===parent&&e.data?.type==='ocean-experiment-visibility')active=!!e.data.active;});
function tick(stamp){requestAnimationFrame(tick);const dt=Math.min(.05,(stamp-last)/1000||0);last=stamp;if(!active||document.hidden)return;if(!paused)states[selected].time+=dt;uniforms.time.value=states[selected].time;controls.update();renderer.render(scene,camera);}requestAnimationFrame(tick);
}catch(error){$('error').hidden=false;$('error').textContent='岸线场景未能加载：'+error.message;console.error(error);}
