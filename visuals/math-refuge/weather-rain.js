import * as THREE from 'three';
import {BUILDING_SCALE as S} from './site-layout.js?v44-hall-clearance';
export function sheltered(x,y,z,roofs){return roofs.some(r=>x>=r[0]-.08&&x<=r[1]+.08&&z>=r[2]-.08&&z<=r[3]+.08&&y<r[4]);}
export function createRain(scene){
 const count=1800,positions=new Float32Array(count*3),shape=new Float32Array(count*3),seeds=new Float32Array(count*4),roofs=[];
 const hash=n=>{const v=Math.sin(n*127.1+311.7)*43758.5453;return v-Math.floor(v);};
 for(let i=0;i<seeds.length;i++)seeds[i]=hash(i+1);
 scene.traverse(o=>{const d=o.userData;if(d.bounds?.length===4&&Number.isFinite(d.floorY)&&Number.isFinite(d.clearHeight))roofs.push([...d.bounds.map(v=>v*S),d.floorY*S+d.clearHeight+.25]);});
 const geometry=new THREE.InstancedBufferGeometry();geometry.setAttribute('position',new THREE.Float32BufferAttribute([-1,-.5,0,1,-.5,0,1,.5,0,-1,.5,0],3));geometry.setIndex([0,1,2,0,2,3]);geometry.setAttribute('dropPosition',new THREE.InstancedBufferAttribute(positions,3).setUsage(THREE.DynamicDrawUsage));geometry.setAttribute('dropShape',new THREE.InstancedBufferAttribute(shape,3).setUsage(THREE.DynamicDrawUsage));
 const uniforms={opacity:{value:0},wind:{value:0}};
 const material=new THREE.ShaderMaterial({transparent:true,depthWrite:false,uniforms,vertexShader:`attribute vec3 dropPosition,dropShape;uniform float wind;varying vec2 vUv;varying float strength;void main(){vec4 eye=viewMatrix*vec4(dropPosition,1.);vec3 fall=mat3(viewMatrix)*vec3(-wind*.015,1.,-.025);vec2 along=normalize(fall.xy+vec2(.000001));vec2 across=vec2(along.y,-along.x);eye.xy+=along*position.y*dropShape.x+across*position.x*dropShape.y;vUv=position.xy;strength=dropShape.z*smoothstep(1.,3.,-eye.z)*(1.-smoothstep(15.,25.,length(eye.xyz)));gl_Position=projectionMatrix*eye;}`,fragmentShader:`uniform float opacity;varying vec2 vUv;varying float strength;void main(){float edge=exp(-4.*vUv.x*vUv.x)*(1.-smoothstep(.55,1.,abs(vUv.x)));float taper=pow(max(0.,1.-4.*vUv.y*vUv.y),1.5);gl_FragColor=vec4(.66,.75,.80,opacity*strength*edge*taper);}`});
 const mesh=new THREE.Mesh(geometry,material);mesh.name='Weather rain streaks';mesh.frustumCulled=false;mesh.visible=false;scene.add(mesh);let elapsed=0,drift=0;
 return {mesh,roofs,update(dt,camera,weather,day,reduced=false){
   const intensity=Math.min(1,Math.max(0,weather.rain)/3);mesh.visible=intensity>.002;if(!mesh.visible)return;
   if(!reduced){elapsed+=Math.min(dt,.1);drift+=Math.min(dt,.1)*weather.wind*.035;}const n=count;geometry.instanceCount=n;uniforms.opacity.value=(.18+.22*day)*intensity;uniforms.wind.value=weather.wind;
   const cx=camera.position.x-24,cz=camera.position.z-24,base=camera.position.y-12,wrap=(v,size)=>(v%size+size)%size;
   for(let i=0;i<n;i++){const k=i*4,j=i*3,speed=9+seeds[k+3]*6;const x=cx+wrap(seeds[k]*48+drift-cx,48),z=cz+wrap(seeds[k+1]*48+elapsed*.15-cz,48),y=base+wrap(seeds[k+2]*32-elapsed*speed-base,32),length=.10+seeds[k+3]**2*.35;
    positions[j]=x;positions[j+1]=y;positions[j+2]=z;shape[j]=length;shape[j+1]=.004+seeds[k+2]*.007;
    shape[j+2]=sheltered(x,y-length/2,z,roofs)?0:.35+.65*seeds[k+1];
   }geometry.attributes.dropPosition.needsUpdate=true;geometry.attributes.dropShape.needsUpdate=true;
 },dispose(){geometry.dispose();material.dispose();scene.remove(mesh);}};
}
