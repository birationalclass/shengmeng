import * as T from '../3d/vendor/three.module.js';
import {jointMotion} from './architectural-motion.mjs?v=living1';
import {installPoolBoats} from './pool-boats.mjs?v=pool1';
const mat=(color,extra={})=>new T.MeshStandardMaterial({color,roughness:.7,...extra});
export function ecnuCampus(a,p){
 p.userData.domain='ecnu-reflecting-pool';
 const stone=mat(0xdce7e6),edge=mat(0x93c4dc,{metalness:.15,roughness:.4}),floor=mat(0xc6e0e6,{roughness:.6}),pink=mat(0xe5c6cf),green=mat(0x53764d);
 const surface=(mesh,name)=>{mesh.userData.poolSurface=true;mesh.userData.landmark=name;return mesh;};
 surface(a.cylinder(p,12.9,.24,[0,.18,0],stone),'pool-foundation');
 surface(a.cylinder(p,11.68,.028,[0,.318,0],floor),'pool-floor');
 const rim=surface(a.mesh(p,new T.RingGeometry(11.68,12.9,128),stone,[0,.79,0]),'pool-rim');rim.rotation.x=-Math.PI/2;
 // The vertical inner wall and pale-blue coping make the water depth legible.
 const wall=surface(a.mesh(p,new T.CylinderGeometry(11.68,11.68,.46,128,1,true),mat(0xafd1da,{side:T.DoubleSide}),[0,.56,0]),'pool-wall');
 surface(a.torus(p,11.7,.055,[0,.79,0],edge),'pool-inner-edge');surface(a.torus(p,12.88,.04,[0,.79,0],edge),'pool-outer-edge');
 for(let k=0;k<64;k++){const q=k*Math.PI/32;surface(a.rod(p,[Math.sin(q)*11.76,.796,Math.cos(q)*11.76],[Math.sin(q)*12.83,.796,Math.cos(q)*12.83],.009,edge),'pool-coping-joint');}
 // A shallow mosaic seal rests on the bottom, well below the water surface.
 surface(a.cylinder(p,2.08,.008,[0,.336,9.15],stone),'ecnu-official-seal');
 surface(a.torus(p,2.06,.018,[0,.349,9.15],edge),'submerged-seal-border');
 if(typeof document!=='undefined'){
  const texture=new T.TextureLoader().load(new URL('./images/ecnu-seal.png',import.meta.url).href,t=>{const canvas=document.createElement('canvas');canvas.width=768;canvas.height=779;const ctx=canvas.getContext('2d');ctx.drawImage(t.image,0,0,768,779);const pixels=ctx.getImageData(0,0,768,779),d=pixels.data;for(let i=0;i<d.length;i+=4){const ink=Math.min(1,(255-d[i+1])/224);d[i]=147;d[i+1]=196;d[i+2]=220;d[i+3]=Math.round(d[i+3]*ink);}ctx.putImageData(pixels,0,0);t.image=canvas;t.needsUpdate=true;});texture.colorSpace=T.SRGBColorSpace;
  const image=a.mesh(p,new T.PlaneGeometry(3.76*5907/5988,3.76),new T.MeshBasicMaterial({map:texture,transparent:true,depthWrite:false}),[0,.353,9.15]);image.rotation.x=-Math.PI/2;image.renderOrder=1;image.userData.landmark='submerged-seal-image';
 }
 const waterMaterial=new T.ShaderMaterial({transparent:true,depthWrite:false,uniforms:{uTime:{value:0}},
  vertexShader:`varying vec3 vPosition; void main(){vPosition=position;gl_Position=projectionMatrix*modelViewMatrix*vec4(position,1.0);}`,
  fragmentShader:`uniform float uTime; varying vec3 vPosition;
   void main(){vec2 p=vPosition.xy;float w=sin(p.x*2.2+p.y*1.4-uTime*.6)*sin(p.y*2.6-p.x*.7+uTime*.43);float glint=pow(max(0.0,w),5.0);float rings=pow(max(0.0,sin(length(p-vec2(0.0,-9.15))*6.0-uTime*.8)),28.0)*.08;vec3 c=mix(vec3(.045,.32,.43),vec3(.78,.95,1.0),glint*.55+rings);gl_FragColor=vec4(c,.30+glint*.18);
   #include <tonemapping_fragment>
   #include <colorspace_fragment>
  }`});
 const water=surface(a.mesh(p,new T.CircleGeometry(11.66,128),waterMaterial,[0,.70,0]),'pool-water');water.rotation.x=-Math.PI/2;water.renderOrder=2;a.poolWater??=[];a.poolWater.push(waterMaterial);
 a.poolRipples??=[];for(const [x,z]of [[-6.8,-7.2],[6.8,-7.2],[0,9.0]])for(let j=0;j<2;j++){const points=Array.from({length:64},(_,k)=>new T.Vector3(Math.sin(k*Math.PI/32),0,Math.cos(k*Math.PI/32))),line=new T.LineLoop(new T.BufferGeometry().setFromPoints(points),new T.LineBasicMaterial({color:0x6dabbf,transparent:true,opacity:.3,depthWrite:false}));line.position.set(x,.715,z);line.renderOrder=3;p.add(line);a.poolRipples.push({line,phase:j*.5+Math.abs(x)*.1});}
 // Retain the four cherry trees, on the dry outer bank.
 for(const side of [-1,1])for(const z of [1.8,5.6]){
  const x=side*Math.sqrt(12.1**2-z*z);const planter=a.cylinder(p,.65,.12,[x,.85,z],stone);planter.userData.landmark='cherry-planter';a.cylinder(p,.12,1.85,[x,1.84,z],a.materials.wood);
  const crown=new T.Group();crown.position.set(x,3.0,z);crown.userData.landmark='cherry-tree';p.add(crown);
  for(let k=0;k<9;k++){const q=k*2.4,leaf=a.mesh(crown,new T.IcosahedronGeometry(.46,1),pink,[Math.sin(q)*.62,(k%3)*.18,Math.cos(q)*.62]);leaf.scale.y=.65;}
  jointMotion(a,crown,{axis:'z',amplitude:.035,speed:.45,phase:z});
 }
 for(const side of [-1,1])for(let j=0;j<5;j++){const z=2.3+j*.64,x=side*Math.sqrt(12.3**2-z*z);a.mesh(p,new T.IcosahedronGeometry(.27,1),green,[x,1.03,z]);}
 installPoolBoats(a,p);return p;
}
