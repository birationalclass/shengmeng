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
 const noise=densityTexture(device.noiseSize||64),target=new T.WebGLRenderTarget(size,size/2,{type:renderer.extensions.has('EXT_color_buffer_float')?T.HalfFloatType:T.UnsignedByteType,depthBuffer:false,stencilBuffer:false});target.texture.wrapS=T.RepeatWrapping;const targets=[target,target.clone()];let front=0;
 const coverageQuantiles=[0.03557725293328986, 0.2114051797759194, 0.25193887045735985, 0.28106544011743545, 0.3049933947053252, 0.3278578215640751, 0.34643832371026445, 0.3650978786462471, 0.3822517187577652, 0.39874209191205334, 0.4152664543193353, 0.43056755824837767, 0.44513135375766877, 0.4605954689951862, 0.47483748649710744, 0.4885058515597245, 0.5032210031166335, 0.5174003195924649, 0.5313472915548605, 0.5449129211608166, 0.5599380736831316, 0.5748990645872083, 0.5901049132148516, 0.6046956450505222, 0.6205398731434861, 0.636390777259328, 0.6543391344117473, 0.6734547487437641, 0.6942006268157725, 0.7184535550312877, 0.7466102422960983, 0.7871598078048733, 0.9507641646631495];
 const thresholdFor=c=>{const v=(1-Math.max(0,Math.min(1,c)))*32,i=Math.min(31,Math.floor(v));return coverageQuantiles[i]+(coverageQuantiles[i+1]-coverageQuantiles[i])*(v-i);};
 const uniforms={coverageThreshold:{value:.5},marchSteps:{value:steps},origin:{value:new T.Vector3(0,.015,0)},volume:{value:noise},coverage:{value:0},sun:{value:new T.Vector3(0,1,0)},sunTint:{value:new T.Color('white')},day:{value:1},storm:{value:0},offset:{value:new T.Vector2()}};
 const material=new T.ShaderMaterial({glslVersion:T.GLSL3,uniforms,depthTest:false,depthWrite:false,vertexShader:'out vec2 cloudUV;void main(){cloudUV=uv;gl_Position=vec4(position.xy,0.,1.);}',fragmentShader:`
 precision highp float;precision highp sampler3D;in vec2 cloudUV;out vec4 cloudResult;
 uniform sampler3D volume;uniform float marchSteps;uniform float coverageThreshold,coverage,day,storm;uniform vec3 sun,sunTint,origin;uniform vec2 offset;
 float topDistance(vec3 d,float height){float r=6360.+origin.y,b=r*d.y;return -b+sqrt(b*b+pow(6360.+height,2.)-r*r);}
 float regionalHash(vec2 p){vec3 q=fract(vec3(p.xyx)*.1031);q+=dot(q,q.yzx+33.33);return fract((q.x+q.y)*q.z);}
 float regionalNoise(vec2 p){vec2 c=floor(p),f=fract(p);f=f*f*(3.-2.*f);return mix(mix(regionalHash(c),regionalHash(c+vec2(1,0)),f.x),mix(regionalHash(c+vec2(0,1)),regionalHash(c+vec2(1,1)),f.x),f.y);}
 float density(vec3 p,bool detailed){
  vec2 ground=p.xz-offset;
  vec2 warped=ground+vec2(regionalNoise(ground*.031),regionalNoise(ground*.027+19.))*8.;
  float region=.68*regionalNoise(warped*.065)+.32*regionalNoise(warped*.151+37.);
  // Regional coverage, independent of local erosion: clear corridors between cloud banks.
  float mask=smoothstep(coverageThreshold-.035,coverageThreshold+.035,region);
  mask=mix(mask,1.,smoothstep(.85,1.,coverage));
  float type=regionalNoise(ground*.09+71.);
  float altitude=length(p+vec3(0.,6360.,0.))-6360.;
  float base=mix(1.3,1.7,type),thickness=mix(.55,1.35,type);
  float h=(altitude-base)/thickness;if(h<=0.||h>=1.||mask<.001)return 0.;
  vec3 uv=vec3(warped.x*.14,h*.23,warped.y*.14);
  vec3 n=texture(volume,uv).rgb;
  float shape=n.r*.78+n.g*.22;
  float detail=detailed?texture(volume,uv*3.7+vec3(.13,.21,.07)).g:.65;
  float profile=smoothstep(0.,.12,h)*(1.-smoothstep(mix(.3,.6,type),1.,h));
  float body=max(0.,shape-mix(.48,.32,coverage))*5.5;
  body=max(0.,body-(1.-detail)*mix(.18,.36,type));
  return body*profile*mask*smoothstep(0.,.06,coverage);
 }
 void main(){if(coverage<.0001){cloudResult=vec4(0.);return;}float az=(cloudUV.x-.5)*6.2831853,elevation=cloudUV.y*cloudUV.y*1.5707963;vec3 d=vec3(cos(az)*cos(elevation),sin(elevation),sin(az)*cos(elevation));float start=topDistance(d,1.3),end=min(topDistance(d,3.1),start+35.);float stepSize=(end-start)/marchSteps;float jitter=fract(sin(dot(gl_FragCoord.xy,vec2(12.9898,78.233)))*43758.5453);vec3 color=vec3(0.);float transmittance=1.;float mu=dot(d,sun),forward=.10+.055*(1.-.65*.65)/pow(max(.04,1.+.65*.65-2.*.65*mu),1.5);
 for(int i=0;i<32;i++){if(float(i)>=marchSteps)break;vec3 p=origin+d*(start+(float(i)+.2+.6*jitter)*stepSize);float rho=density(p,true);if(rho>.001){float optical=0.;for(int j=0;j<2;j++){float dist=.25+float(j)*.60;optical+=density(p+sun*dist,false)*.60;}float shadow=exp(-optical*5.);float a=1.-exp(-rho*stepSize*4.2);float h=clamp((length(p+vec3(0.,6360.,0.))-6360.-1.3)/1.8,0.,1.);vec3 ambient=mix(vec3(.19,.25,.33),vec3(.52,.60,.69),h)*(.008+.992*day)*(1.-storm*.38);vec3 direct=sunTint*shadow*(.65+forward)*day*(1.-storm*.55);color+=transmittance*a*(ambient+direct);transmittance*=1.-a;if(transmittance<.015)break;}}
 float distanceFade=exp(-start*.025);cloudResult=vec4(color*distanceFade,(1.-transmittance)*distanceFade);}`});
 const scene=new T.Scene(),quad=new T.Mesh(new T.PlaneGeometry(2,2),material),camera=new T.Camera();scene.add(quad);
 const tileCount=device.mobile?2:4;let key='',last=-Infinity,pending=null;
 function capture(u){
  uniforms.origin.value.copy(u.cloudOrigin.value);uniforms.coverage.value=u.cloud.value;uniforms.coverageThreshold.value=thresholdFor(u.cloud.value);uniforms.sun.value.copy(u.sunPosition.value);
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
 function publish(u,now,next,first){
  const prior=front;front=next;last=now;
  u.cloudMap.value=targets[front].texture;u.cloudMapPrevious.value=targets[first?front:prior].texture;u.cloudBlend.value=first?1:0;
 }
 return {setQuality(level){const q=CLOUD_LEVELS[level]||CLOUD_LEVELS.medium;if(size===q.size&&steps===q.steps)return;size=q.size;steps=q.steps;interval=q.interval;uniforms.marchSteps.value=steps;targets.forEach(t=>t.setSize(size,size/2));key='';pending=null;last=-Infinity;},get texture(){return targets[front].texture;},update(u,now=performance.now()){
  if(u.cloud.value<.0001){pending=null;key='';u.useVolumeClouds.value=0;return;}u.useVolumeClouds.value=1;
  u.cloudBlend.value=Math.min(1,(now-last)/interval);
  if(pending){
   renderTile(targets[pending.target],pending.tile++,tileCount);
   if(pending.tile===tileCount){key=pending.key;publish(u,now,pending.target,false);pending=null;}
   return;
  }
  const nextKey=[u.cloud.value,u.day.value,u.storm.value,...u.sunPosition.value.toArray(),...u.cloudOffset.value.toArray(),...u.cloudOrigin.value.toArray()].join(',');
  if(nextKey===key||now-last<interval)return;
  capture(u);const next=1-front;
  // Prepare the initial panorama before entry. Later refreshes never publish a
  // partially drawn image, nor overwrite the previous frame during its blend.
  if(!key){renderTile(targets[next],0,1);key=nextKey;publish(u,now,next,true);return;}
  pending={key:nextKey,target:next,tile:1};renderTile(targets[next],0,tileCount);
 },dispose(){noise.dispose();targets.forEach(t=>t.dispose());quad.geometry.dispose();material.dispose();}};
}
