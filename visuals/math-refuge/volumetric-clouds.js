import {cloudCoverageArea,coverageThreshold,distantCloudCoverage} from './cloud-coverage.js';
import * as T from 'three';
import {CLOUD_LEVELS} from './graphics-settings.js?v84-display';
// Persistent 3D Perlin-like value/Worley density volume, not screen-space cloud stamps.
function densityTexture(N=64){
 const data=new Uint8Array(N*N*N*4),hash=(x,y,z)=>{let n=Math.imul(x,374761393)^Math.imul(y,668265263)^Math.imul(z,2147483647);n=Math.imul(n^(n>>>13),1274126177);return ((n^(n>>>16))>>>0)/4294967296;};
 const noise=(x,y,z,p)=>{const a=Math.floor(x),b=Math.floor(y),c=Math.floor(z),smooth=v=>v*v*(3-2*v),u=smooth(x-a),v=smooth(y-b),w=smooth(z-c);let sum=0;for(let k=0;k<2;k++)for(let j=0;j<2;j++)for(let i=0;i<2;i++)sum+=hash((a+i+p)%p,(b+j+p)%p,(c+k+p)%p)*(i?u:1-u)*(j?v:1-v)*(k?w:1-w);return sum;};
 for(let z=0;z<N;z++)for(let y=0;y<N;y++)for(let x=0;x<N;x++){
  const scale=64/N,fx=x*scale/8,fy=y*scale/8,fz=z*scale/8,ix=Math.floor(fx),iy=Math.floor(fy),iz=Math.floor(fz);let nearest=3;
  for(let k=-1;k<=1;k++)for(let j=-1;j<=1;j++)for(let i=-1;i<=1;i++){const a=ix+i,b=iy+j,c=iz+k,hx=(a+8)%8,hy=(b+8)%8,hz=(c+8)%8;const dx=a+hash(hx,hy,hz)-fx,dy=b+hash(hx+31,hy,hz)-fy,dz=c+hash(hx,hy+51,hz)-fz;nearest=Math.min(nearest,dx*dx+dy*dy+dz*dz);}
  const n=.62*noise(x*scale/16,y*scale/16,z*scale/16,4)+.28*noise(x*scale/8,y*scale/8,z*scale/8,8)+.1*noise(x*scale/4,y*scale/4,z*scale/4,16),p=((z*N+y)*N+x)*4;
  data[p]=Math.round(n*255);data[p+1]=Math.round((1-Math.min(1,Math.sqrt(nearest)))*255);data[p+2]=Math.round(noise(x*scale/2,y*scale/2,z*scale/2,32)*255);data[p+3]=255;
 }
 const texture=new T.Data3DTexture(data,N,N,N);texture.format=T.RGBAFormat;texture.minFilter=texture.magFilter=T.LinearFilter;texture.wrapS=texture.wrapT=texture.wrapR=T.RepeatWrapping;texture.unpackAlignment=1;texture.needsUpdate=true;return texture;
}
export function createVolumetricClouds(renderer,device={}){
 if(!renderer?.isWebGLRenderer||device.safe)return null;
 let size=device.cloudSize||512,steps=device.cloudSteps||24,interval=device.cloudInterval||250;
 const noise=densityTexture(device.noiseSize||64),target=new T.WebGLRenderTarget(size,size/2,{type:renderer.extensions.has('EXT_color_buffer_float')?T.HalfFloatType:T.UnsignedByteType,depthBuffer:false,stencilBuffer:false});target.texture.wrapS=T.RepeatWrapping;const targets=[target,target.clone(),target.clone()];let front=0,previous=0;
 let areaKey='',area,thresholdKey='',calibratedThreshold=.5,calibratedDistantThreshold=.5;
 const windows=[new T.Vector2(1,0),new T.Vector2(-1,0)];
 const uniforms={seedOffset:{value:new T.Vector2()},sunriseBearing:{value:windows[0]},sunsetBearing:{value:windows[1]},coverageThreshold:{value:.5},distantThreshold:{value:.5},marchSteps:{value:steps},origin:{value:new T.Vector3(0,.015,0)},volume:{value:noise},coverage:{value:0},sun:{value:new T.Vector3(0,1,0)},sunTint:{value:new T.Color('white')},day:{value:1},storm:{value:0},offset:{value:new T.Vector2()}};
 const material=new T.ShaderMaterial({glslVersion:T.GLSL3,uniforms,depthTest:false,depthWrite:false,vertexShader:'out vec2 cloudUV;void main(){cloudUV=uv;gl_Position=vec4(position.xy,0.,1.);}',fragmentShader:`
 precision highp float;precision highp sampler3D;in vec2 cloudUV;out vec4 cloudResult;
 uniform sampler3D volume;uniform float marchSteps;uniform float coverageThreshold,distantThreshold,coverage,day,storm;uniform vec3 sun,sunTint,origin;uniform vec2 offset,seedOffset,sunriseBearing,sunsetBearing;
 float topDistance(vec3 d,float height){float r=6360.+origin.y,b=r*d.y;return -b+sqrt(max(0.,b*b+pow(6360.+height,2.)-r*r));}
 float regionalHash(vec2 p){vec3 q=fract(vec3(p.xyx)*.1031);q+=dot(q,q.yzx+33.33);return fract((q.x+q.y)*q.z);}
 float regionalNoise(vec2 p){vec2 c=floor(p),f=fract(p);f=f*f*(3.-2.*f);return mix(mix(regionalHash(c),regionalHash(c+vec2(1,0)),f.x),mix(regionalHash(c+vec2(0,1)),regionalHash(c+vec2(1,1)),f.x),f.y);}
 float density(vec3 p,bool detailed){
  vec2 ground=p.xz-offset-seedOffset;
  vec2 warped=ground+vec2(regionalNoise(ground*.031),regionalNoise(ground*.027+19.))*8.;
  float region=.68*regionalNoise(warped*.065)+.32*regionalNoise(warped*.151+37.);
  // Regional coverage, independent of local erosion: clear corridors between cloud banks.
  float distanceWeight=smoothstep(20.,60.,length(p.xz-origin.xz));
  float localThreshold=mix(coverageThreshold,distantThreshold,distanceWeight);
  float mask=smoothstep(localThreshold-.035,localThreshold+.035,region);
  float type=regionalNoise(ground*.09+71.);
  float altitude=length(p+vec3(0.,6360.,0.))-6360.;
  // Kilometre-scale rounded billows disturb both boundaries, not a flat slab.
  float billow=regionalNoise(warped*.65+13.);
  float base=1.32+.24*type+.18*(billow-.5);
  float thickness=.75+.90*type+.40*billow;
  float h=(altitude-base)/thickness;if(h<=0.||h>=1.||mask<.001)return 0.;
  vec3 uv=vec3(warped.x*.12,h*.52,warped.y*.12);
  vec3 n=texture(volume,uv).rgb;
  float shape=n.r*.52+n.g*.48;
  float detail=texture(volume,uv*3.7+vec3(.13,.21,.07)).g;
  float profile=pow(max(0.,4.*h*(1.-h)),.65);
  float body=max(0.,shape-mix(.48,.32,coverage))*5.5;
  body=max(0.,body-(1.-detail)*mix(.10,.22,type));
  return body*profile*mask*smoothstep(0.,.06,coverage);
 }
 void main(){if(coverage<.0001||origin.y>=3.8){cloudResult=vec4(0.);return;}float az=(cloudUV.x-.5)*6.2831853,elevation=cloudUV.y*cloudUV.y*1.5707963;vec3 d=vec3(cos(az)*cos(elevation),sin(elevation),sin(az)*cos(elevation));float start=origin.y>=1.2?0.:max(0.,topDistance(d,1.2)),end=min(topDistance(d,3.8),start+35.);float stepSize=(end-start)/marchSteps;float jitter=fract(sin(dot(gl_FragCoord.xy,vec2(12.9898,78.233)))*43758.5453);vec3 color=vec3(0.);float transmittance=1.;float mu=dot(d,sun),forward=.10+.055*(1.-.65*.65)/pow(max(.04,1.+.65*.65-2.*.65*mu),1.5);
 for(int i=0;i<48;i++){if(float(i)>=marchSteps)break;vec3 p=origin+d*(start+(float(i)+.2+.6*jitter)*stepSize);float rho=density(p,true);if(rho>.001){float optical=0.;for(int j=0;j<2;j++){float dist=.25+float(j)*.60;optical+=density(p+sun*dist,false)*.60;}float shadow=exp(-optical*5.);float a=1.-exp(-rho*stepSize*4.2);float h=clamp((length(p+vec3(0.,6360.,0.))-6360.-1.3)/1.8,0.,1.);vec3 ambient=mix(vec3(.19,.25,.33),vec3(.52,.60,.69),h)*(.008+.992*day)*(1.-storm*.38);vec3 direct=sunTint*shadow*(.65+forward)*day*(1.-storm*.55);color+=transmittance*a*(ambient+direct);transmittance*=1.-a;if(transmittance<.015)break;}}
 // Distance haze changes radiance, not optical coverage: distant thick clouds still occlude the sun.
 float distanceFade=exp(-start*.025);vec3 aerialTint=vec3(.52,.60,.69)*(.008+.992*day);cloudResult=vec4(mix(aerialTint*(1.-transmittance),color,distanceFade),1.-transmittance);}`});
 const scene=new T.Scene(),quad=new T.Mesh(new T.PlaneGeometry(2,2),material),camera=new T.Camera();scene.add(quad);
 const tileCount=device.mobile?8:16;let key='',last=-Infinity,pending=null;
 function capture(u){
  if(u.cloudSeedOffset)uniforms.seedOffset.value.copy(u.cloudSeedOffset.value);
  uniforms.origin.value.copy(u.cloudOrigin.value);uniforms.coverage.value=u.cloud.value;uniforms.coverageThreshold.value=calibratedThreshold;uniforms.distantThreshold.value=calibratedDistantThreshold;uniforms.sun.value.copy(u.sunPosition.value);
  uniforms.sunTint.value.copy(u.sunColor.value);uniforms.day.value=u.day.value;uniforms.storm.value=u.storm.value;uniforms.offset.value.copy(u.cloudOffset.value);
 }
 function renderTile(target,tile,count){
  const y=Math.floor(tile*size/2/count),end=Math.floor((tile+1)*size/2/count);
  // Keep the full viewport/UVs: the scissor only limits fragment work. Scissor
  // state belongs to this target, so restoring the prior target restores its state.
  target.scissor.set(0,y,size,end-y);target.scissorTest=true;
  const previous=renderer.getRenderTarget(),auto=renderer.autoClear;
  try{renderer.autoClear=true;renderer.setRenderTarget(target);renderer.render(scene,camera);}
  finally{renderer.setRenderTarget(previous);renderer.autoClear=auto;}
 }
 let hasFrame=false,blendInterval=interval;
 function publish(u,now,next,first){
  const prior=front;previous=prior;front=next;last=now;blendInterval=interval;hasFrame=true;
  u.cloudMap.value=targets[front].texture;u.cloudMapPrevious.value=targets[first?front:prior].texture;u.cloudBlend.value=first?1:0;
 }
 let preparation;
 return {tileCount,prepare(){return preparation??=(async()=>{
  renderer.initTexture(noise);
  await renderer.compileAsync?.(scene,camera);
  for(const target of targets){renderer.initRenderTarget(target);await new Promise(resolve=>setTimeout(resolve,0));}
 })();},setQuality(level){const q=CLOUD_LEVELS[level]||CLOUD_LEVELS.medium;if(size===q.size&&steps===q.steps)return;size=q.size;steps=q.steps;interval=q.interval;uniforms.marchSteps.value=steps;key='';pending=null;},get texture(){return targets[front].texture;},update(u,now=performance.now()){
  if(u.cloud.value<.0001){pending=null;key='';u.useVolumeClouds.value=0;return;}u.useVolumeClouds.value=1;
  u.cloudBlend.value=Math.min(1,(now-last)/blendInterval);
  if(pending){
   if(pending.tile<tileCount)renderTile(targets[pending.target],pending.tile++,tileCount);
   if(pending.tile===tileCount&&(!hasFrame||now-last>=blendInterval)){key=pending.key;publish(u,now,pending.target,!hasFrame);pending=null;}
   return;
  }
  const bearings=[u.sunriseBearing?.value||windows[0],u.sunsetBearing?.value||windows[1]];
  const seed=u.cloudSeedOffset?.value?.toArray()||[0,0];
  const nextAreaKey=bearings.map(v=>v.toArray().join(',')).join(';')+':'+seed.join(',');
  if(nextAreaKey!==areaKey){windows.forEach((v,i)=>v.copy(bearings[i]));area=cloudCoverageArea(windows.map(v=>v.toArray()),seed);areaKey=nextAreaKey;thresholdKey='';}
  const nextThresholdKey=areaKey+':'+u.cloud.value.toFixed(2);
  if(nextThresholdKey!==thresholdKey){calibratedThreshold=coverageThreshold(area,u.cloud.value);calibratedDistantThreshold=coverageThreshold(area,distantCloudCoverage(u.cloud.value));thresholdKey=nextThresholdKey;}
  const nextKey=[areaKey,u.cloud.value,u.day.value,u.storm.value,...u.sunPosition.value.toArray(),...u.cloudOffset.value.toArray(),...u.cloudOrigin.value.toArray()].join(',');
  if(nextKey===key)return;
  capture(u);const next=targets.findIndex((_,i)=>i!==front&&i!==previous);targets[next].setSize(size,size/2);
  // Triple buffering computes the next panorama while the two visible maps blend.
  // Never render into either visible map. Quality changes retain bounded tile work.
  // Publish only a complete panorama; keep the previous texture until then.
  pending={key:nextKey,target:next,tile:1};renderTile(targets[next],0,tileCount);
 },dispose(){noise.dispose();targets.forEach(t=>t.dispose());quad.geometry.dispose();material.dispose();}};
}
