import * as THREE from '../3d/vendor/three.module.js';
import {modelGLSL} from './ocean-renderer.js';
import {coastalOptics,capillaryNormals,opticalBody,opticalReflection,opticalBeach} from './coastal-optics.js';
import {makeWaveSpectrum} from './wave-spectrum.js';
import {foamVisibility,breakerVisibility,breakerDetailEnabled} from './ocean-detail.js';
import {ringPoint,branchPoint,bedHeight,tideLevel,terrainGLSL,waveGLSL} from './elliptic-model.js';

// Math Refuge's panoramic horizon: below-horizon sky and the distant sea
// share grazing radiance. The radial blend completes before the square mesh edge.
const horizonGLSL=`
uniform float uOceanLevel;
vec3 grazingSea(vec3 ray){
 return sky(normalize(vec3(ray.x,.00001,ray.z)),false)*vec3(.76,.84,.89);
}
// Analytic flat-water continuation beyond the detailed mesh, in world-ray
// coordinates. Unlike a solid horizon strip, it retains view-dependent sky
// reflections, water Fresnel and the same GGX sunlight model as 02.
vec3 distantSea(vec3 ray){
 ray=normalize(ray);vec3 view=-ray,n=vec3(0.,1.,0.),sd=sunDirection();
 float day=smoothstep(5.,22.,uSun),dusk=1.-smoothstep(-3.,3.,uSun);
 vec3 r=reflect(ray,n);r.y=max(.002,r.y);
 vec3 reflected=sky(r,true);
 reflected-=vec3(5.,3.75,1.85)*(1.-smoothstep(.009,.012,length(r-sd)))*(1.-dusk*.7);
 reflected=max(reflected,vec3(0.));
 float fresnel=.0204+.9796*pow(1.-sat(view.y),5.);
 vec3 body=mix(vec3(.014,.092,.105),vec3(.025,.24,.255),day);
 vec3 col=mix(body,reflected,fresnel);
 vec3 halfV=normalize(sd+view);float nh=max(.001,halfV.y);
 float nv=max(.03,view.y),nl=max(0.,sd.y),alpha2=.00016;
 float denom=nh*nh*(alpha2-1.)+1.;float distribution=alpha2/(PI*denom*denom);
 float gv=2.*nv/(nv+sqrt(alpha2+(1.-alpha2)*nv*nv));
 float gl=2.*nl/max(.001,nl+sqrt(alpha2+(1.-alpha2)*nl*nl));
 float sf=.02+.98*pow(1.-sat(dot(view,halfV)),5.);
 vec3 light=mix(vec3(1.8,.91,.36),vec3(1.4,1.4,1.25),day)*(1.-dusk*.55);
 col+=light*min(18.,distribution*sf*gv*gl/(4.*nv))*smoothstep(-4.,1.,uSun);
 float travel=max(0.,cameraPosition.y-uOceanLevel)/max(.000001,-ray.y);
 float range=travel*length(ray.xz);
 float haze=1.-exp(-pow(range*.000015,1.2));
 return mix(col,grazingSea(ray),haze);
}
vec3 panoramicBackground(vec3 ray){
 float aa=max(fwidth(ray.y),.00003);
 if(ray.y>=aa)return sky(ray,true);
 return mix(distantSea(ray),sky(ray,true),smoothstep(-aa,aa,ray.y));
}
`;
const environment=modelGLSL.environment;
const fragment='#define COAST_FRAGMENT\n'+environment+terrainGLSL+horizonGLSL;
function oceanGrid(n=256){
 const geo=new THREE.PlaneGeometry(2,2,n,n);geo.rotateX(-Math.PI/2);
 return geo;
}
// Sand uses an explicit ribbon mesh so the 100 m band remains continuous
// even when a distant adaptive ocean triangle spans hundreds of metres.
function ribbon(point,count,start,end){
 const offsets=[-410,-240,-150,-90,-65,-52,-48,-40,-25,-10,0,10,25,40,48,52,65,90,150,240,410];
 const vertices=[],indices=[];
 for(let i=0;i<=count;i++){
  const t=start+(end-start)*i/count,p=point(t),a=point(t-.0001),b=point(t+.0001);
  const dx=b[0]-a[0],dz=b[1]-a[1],length=Math.hypot(dx,dz);
  for(const offset of offsets){
   const x=p[0]-dz/length*offset,z=p[1]+dx/length*offset;
   vertices.push(x,bedHeight(Math.abs(offset),x,z),z);
  }
 }
 const cols=offsets.length;
 for(let i=0;i<count;i++)for(let j=0;j<cols-1;j++){
  const a=i*cols+j,b=a+cols;indices.push(a,b,a+1,a+1,b,b+1);
 }
 const geo=new THREE.BufferGeometry();geo.setAttribute('position',new THREE.Float32BufferAttribute(vertices,3));geo.setIndex(indices);geo.computeBoundingSphere();
 return geo;
}

export class EllipticRenderer{
 constructor(canvas,field,options={}){
  this.renderer=options.renderer||new THREE.WebGLRenderer({canvas,antialias:true,powerPreference:'high-performance'});
  if(!options.renderer){this.renderer.setPixelRatio(1);
  this.renderer.debug.onShaderError=(gl,program,vs,fs)=>{throw Error(gl.getShaderInfoLog(vs)+'\n'+gl.getShaderInfoLog(fs));};}
  this.scene=new THREE.Scene();this.camera=new THREE.PerspectiveCamera(64,1,.15,18000);
  const waves=makeWaveSpectrum(.35);
  this.uniforms={uDistance:{value:field},uOrigin:{value:new THREE.Vector2()},uNear:{value:8},uTime:{value:7.1},uWave:{value:.6},uWind:{value:.35},uSun:{value:24},uGrid:{value:0},uTide:{value:0},uOceanLevel:{value:0},uWaves:{value:waves.map(w=>new THREE.Vector4(w.x,w.z,w.k,w.amplitude))},uPhases:{value:waves.map(w=>new THREE.Vector2(w.omega,w.phase))}};
  const sky=new THREE.Mesh(new THREE.SphereGeometry(15000,32,16),new THREE.ShaderMaterial({uniforms:this.uniforms,side:THREE.BackSide,depthWrite:false,vertexShader:'varying vec3 vRay;void main(){vRay=position;gl_Position=projectionMatrix*viewMatrix*vec4(position+cameraPosition,1.);}',fragmentShader:environment+horizonGLSL+'varying vec3 vRay;void main(){gl_FragColor=vec4(tone(panoramicBackground(normalize(vRay))),1.);}'}));
  sky.frustumCulled=false;sky.renderOrder=-10;
  if(options.sky!==false)this.scene.add(sky);else{sky.geometry.dispose();sky.material.dispose();}
  // A screen-space ray/plane ocean covers the area outside the detailed mesh
  // and writes actual water depth. A sky-only backdrop cannot hide seabeds.
  this.uniforms.uProjection={value:new THREE.Matrix4()};
  this.uniforms.uInverseProjection={value:new THREE.Matrix4()};
  this.uniforms.uCameraWorld={value:new THREE.Matrix4()};
  const farOcean=new THREE.Mesh(new THREE.PlaneGeometry(2,2),new THREE.ShaderMaterial({uniforms:this.uniforms,depthWrite:true,depthTest:true,
   vertexShader:`uniform mat4 uInverseProjection,uCameraWorld;varying vec3 vRay;
    void main(){vec4 ray=uInverseProjection*vec4(position.xy,1.,1.);vRay=mat3(uCameraWorld)*ray.xyz;gl_Position=vec4(position.xy,0.,1.);}`,
   fragmentShader:environment+horizonGLSL+`uniform mat4 uProjection;varying vec3 vRay;
    void main(){
     vec3 ray=normalize(vRay);if(ray.y>=-.0000001||cameraPosition.y<=uOceanLevel)discard;
     float travel=(uOceanLevel-cameraPosition.y)/ray.y;
     vec3 point=cameraPosition+ray*travel;
     if(length(point.xz-cameraPosition.xz)<9000.)discard;
     vec4 clip=uProjection*viewMatrix*vec4(point,1.);
     gl_FragDepth=clamp(clip.z/clip.w*.5+.5,0.,.9999999);
     gl_FragColor=vec4(tone(distantSea(ray)),1.);
    }` }));
  farOcean.frustumCulled=false;farOcean.renderOrder=-5;this.scene.add(farOcean);
  const sandMaterial=new THREE.ShaderMaterial({uniforms:this.uniforms,defines:{COASTAL_OPTICS:1,CURVED_COAST:1},side:THREE.DoubleSide,
   vertexShader:'varying vec3 vWorld;varying vec2 vCA;void main(){vWorld=position;vCA=position.xz;gl_Position=projectionMatrix*viewMatrix*vec4(position,1.);}',
   fragmentShader:fragment+coastalOptics+`
    varying vec3 vWorld;varying vec2 vCA;
    void main(){
     // Distant water shades its bed analytically. Do not depth-fight a second
     // submerged sand surface when sub-metre separation is no longer resolved.
     if(length(vWorld-cameraPosition)>2000.&&vWorld.y<uTide-.12)discard;
     // Clip self-overlapping submerged ribbon skirts to their nearest curve.
     if(abs(vWorld.y-beachHeight(vCA))>.6&&vWorld.y<-.5)discard;
     float h=beachHeight(vCA),wet=1.-smoothstep(.03,.6,h-uTide-.10);
     vec3 n=bedNormal(vCA),view=normalize(cameraPosition-vWorld),r=reflect(-view,n),col=vec3(0.);
     ${opticalBeach}
     float distance=length(cameraPosition-vWorld);
     col=mix(col,sky(normalize(vec3(-view.x,.005,-view.z)),false),min(.9,1.-exp(-distance*.00010)));
     gl_FragColor=vec4(tone(gridColor(col,vCA)),1.);
    }`});
  this.scene.add(new THREE.Mesh(ribbon(ringPoint,1200,0,Math.PI*2),sandMaterial));
  this.scene.add(new THREE.Mesh(ribbon(branchPoint,2000,-1.7,1.7),sandMaterial));
  const geometry=oceanGrid();
  const adaptive=`uniform float uNear;vec2 gridPoint(vec2 p){return uOrigin+sign(p)*(exp(abs(p)*log(1.+10000./uNear))-1.)*uNear;}`;
  this.uniforms.uFoamVisibility={value:1};
  this.uniforms.uBreakerVisibility={value:1};
  const water=new THREE.ShaderMaterial({uniforms:this.uniforms,defines:{COASTAL_OPTICS:1,CURVED_COAST:1,FOAM_DETAIL:1},side:THREE.DoubleSide,transparent:true,depthWrite:true,forceSinglePass:true,
   vertexShader:environment+terrainGLSL+waveGLSL+adaptive+`
    varying vec3 vWorld,vNormal;varying vec2 vCA;varying vec4 vProfile;
    void main(){
     vec2 p=gridPoint(position.xz);float h=waterLevel(p);
     float e=max(.15,length(p-cameraPosition.xz)*.001);
     vNormal=normalize(vec3(waterLevel(p-vec2(e,0.))-waterLevel(p+vec2(e,0.)),2.*e,waterLevel(p-vec2(0.,e))-waterLevel(p+vec2(0.,e))));
     vWorld=vec3(p.x,h,p.y);vCA=p;vProfile=vec4(0.);gl_Position=projectionMatrix*viewMatrix*vec4(vWorld,1.);
    }`,
   fragmentShader:fragment+coastalOptics+`
    uniform float uFoamVisibility,uBreakerVisibility;
    uniform vec4 uWaves[32];uniform vec2 uPhases[32];
    varying vec3 vWorld,vNormal;varying vec2 vCA;varying vec4 vProfile;
    void main(){
     float bed=beachHeight(vCA),waterThickness=vWorld.y-bed;
     float coverage=smoothstep(0.,.035,waterThickness);if(coverage<.005)discard;
     vec3 view=normalize(cameraPosition-vWorld),n=normalize(vNormal);
     if(n.y<0.)n=-n;
     float distance=length(cameraPosition-vWorld);vec2 uv=vWorld.xz,slope=vec2(0.);float detail=0.;
     // Short gravity waves are too small for the adaptive geometry. Retain
     // their moving normals until their wavelength becomes subpixel.
     vec2 gravitySlope=vec2(0.);
     for(int i=16;i<32;i++){
      vec4 w=uWaves[i];float phase=dot(uv,w.xy)*w.z-uTime*uPhases[i].x+uPhases[i].y;
      float visible=1.-smoothstep(.8,3.,fwidth(phase));
      gravitySlope+=w.xy*w.z*w.w*cos(phase)*visible;
     }
     n=normalize(n+vec3(-gravitySlope.x,0.,-gravitySlope.y)*uWave*1.7*smoothstep(0.,2.5,waterThickness));
     ${capillaryNormals}
     n=normalize(n+vec3(-slope.x,0.,-slope.y)*detail);
     vec3 sd=sunDirection(),r=reflect(-view,n);r.y=max(.002,r.y);
     float day=smoothstep(5.,22.,uSun),dusk=1.-smoothstep(-3.,3.,uSun);
     float fresnel=.0204+.9796*pow(1.-sat(dot(view,n)),5.);
     vec3 reflected=sky(r,true),body=vec3(0.);
     ${opticalBody}
     vec3 reflection=reflected,col=body;vec3 halfV=normalize(sd+view);
     float nh=max(.001,dot(n,halfV));float sf=.02+.98*pow(1.-sat(dot(view,halfV)),5.);
     vec3 light=mix(vec3(1.8,.91,.36),vec3(1.4,1.4,1.25),day)*(1.-dusk*.55);
     ${opticalReflection}
     #if FOAM_DETAIL == 1
     // Derivatives outside the varying branch: only resolved shallow foam
     // evaluates noise/crest/exponential terms. Remote fragments skip them.
     float footprint=max(length(dFdx(vCA)),length(dFdy(vCA)))*1.8;
     float foamLOD=uFoamVisibility*(1.-smoothstep(.35,1.25,footprint))*(1.-smoothstep(60.,180.,distance));
     float shorePhase=(uTide-bed)/.055*.48-uTime*1.5;
     float breakerLOD=uBreakerVisibility*(1.-smoothstep(1.,3.,fwidth(shorePhase)))*(1.-smoothstep(450.,1600.,distance));
     if(max(foamLOD,breakerLOD)>.001&&waterThickness<2.){
      float shore=(uTide-bed)/.055;
      float band=pow(.5+.5*sin(shorePhase+noise(vCA*.016)*2.),3.);
      float foam=band*exp(-pow((waterThickness-.45)/.7,2.))*.12*breakerLOD;
      if(foamLOD>.001){
       float crest=pow(.5+.5*sin(shore*.48-uTime*1.5+noise(vCA*.016)*2.),10.);
       float foamPatch=smoothstep(.35,.70,noise(vCA*1.8+uTime*.18));
       float fine=(exp(-pow((waterThickness-.06)/.13,2.))*.45+crest*exp(-pow((waterThickness-.45)/.7,2.))*.2)*foamPatch;
       foam=mix(foam,fine,foamLOD);
      }
      vec3 white=mix(vec3(.65,.63,.57),vec3(.97,1.,.94),day);
      col=mix(col,white,foam*smoothstep(0.,.05,waterThickness));
     }
     #endif
     float horizontalDistance=length(vCA-cameraPosition.xz);
     float haze=1.-exp(-pow(horizontalDistance*.000015,1.2));
     col=mix(col,grazingSea(-view),haze);
     float horizonBlend=smoothstep(6500.,9500.,horizontalDistance);
     col=mix(col,distantSea(-view),horizonBlend);
     gl_FragColor=vec4(tone(gridColor(col,vCA)),coverage);
    }`});
  this.water=new THREE.Mesh(geometry,water);this.water.frustumCulled=false;this.water.renderOrder=1;this.scene.add(this.water);
  this.waterNear=water;
  this.waterFar=water.clone();this.waterFar.uniforms=this.uniforms;
  this.waterFar.defines={...water.defines,FOAM_DETAIL:0};
  this.foamDetail=true;
 }
 resize(w,h){this.renderer.setSize(w,h,false);this.camera.aspect=w/h;this.camera.updateProjectionMatrix();}
 draw(state,options={}){
  this.uniforms.uTime.value=state.time;this.uniforms.uSun.value=state.sun;this.uniforms.uWave.value=state.wave;
  this.uniforms.uTide.value=tideLevel(state);
  this.uniforms.uOceanLevel.value=this.uniforms.uTide.value;
  const height=Math.max(0,this.camera.position.y-this.uniforms.uTide.value);
  // Keep all corners of the detailed ocean in range as the observer rises.
  const near=Math.max(.15,height*.003),far=Math.max(18000,height+16000);
  if(this.camera.near!==near||this.camera.far!==far){this.camera.near=near;this.camera.far=far;this.camera.updateProjectionMatrix();}
  this.camera.updateMatrixWorld();
  this.uniforms.uProjection.value.copy(this.camera.projectionMatrix);
  this.uniforms.uInverseProjection.value.copy(this.camera.projectionMatrixInverse);
  this.uniforms.uCameraWorld.value.copy(this.camera.matrixWorld);
  this.uniforms.uFoamVisibility.value=foamVisibility(height);
  this.uniforms.uBreakerVisibility.value=breakerVisibility(height);
  this.foamDetail=breakerDetailEnabled(height,this.foamDetail);
  this.water.material=this.foamDetail?this.waterNear:this.waterFar;
  this.renderer.domElement.dataset.foamDetail=this.foamDetail?'near':'off';
  this.renderer.domElement.dataset.foamVisibility=this.uniforms.uFoamVisibility.value.toFixed(3);
  this.renderer.domElement.dataset.breakerVisibility=this.uniforms.uBreakerVisibility.value.toFixed(3);
  this.renderer.domElement.dataset.cameraHeight=height.toFixed(1);
  this.renderer.domElement.dataset.cameraFar=far.toFixed(1);
  this.uniforms.uGrid.value=state.view==='plan'?1:0;
  this.uniforms.uOrigin.value.set(this.camera.position.x,this.camera.position.z);
  this.uniforms.uNear.value=Math.max(8,this.camera.position.y*.15);
  if(options.render!==false)this.renderer.render(this.scene,this.camera);
 }
}
