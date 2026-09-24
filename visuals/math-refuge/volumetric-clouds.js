import * as T from 'three';
// Persistent 3D Perlin-like value/Worley density volume, not screen-space cloud stamps.
function densityTexture(){
 const N=64,data=new Uint8Array(N*N*N*4),hash=(x,y,z)=>{let n=Math.imul(x,374761393)^Math.imul(y,668265263)^Math.imul(z,2147483647);n=Math.imul(n^(n>>>13),1274126177);return ((n^(n>>>16))>>>0)/4294967296;};
 const noise=(x,y,z,p)=>{const a=Math.floor(x),b=Math.floor(y),c=Math.floor(z),smooth=v=>v*v*(3-2*v),u=smooth(x-a),v=smooth(y-b),w=smooth(z-c);let sum=0;for(let k=0;k<2;k++)for(let j=0;j<2;j++)for(let i=0;i<2;i++)sum+=hash((a+i+p)%p,(b+j+p)%p,(c+k+p)%p)*(i?u:1-u)*(j?v:1-v)*(k?w:1-w);return sum;};
 for(let z=0;z<N;z++)for(let y=0;y<N;y++)for(let x=0;x<N;x++){
  const fx=x/8,fy=y/8,fz=z/8,ix=Math.floor(fx),iy=Math.floor(fy),iz=Math.floor(fz);let nearest=3;
  for(let k=-1;k<=1;k++)for(let j=-1;j<=1;j++)for(let i=-1;i<=1;i++){const a=ix+i,b=iy+j,c=iz+k,hx=(a+8)%8,hy=(b+8)%8,hz=(c+8)%8;const dx=a+hash(hx,hy,hz)-fx,dy=b+hash(hx+31,hy,hz)-fy,dz=c+hash(hx,hy+51,hz)-fz;nearest=Math.min(nearest,dx*dx+dy*dy+dz*dz);}
  const n=.62*noise(x/16,y/16,z/16,4)+.28*noise(x/8,y/8,z/8,8)+.1*noise(x/4,y/4,z/4,16),p=((z*N+y)*N+x)*4;
  data[p]=Math.round(n*255);data[p+1]=Math.round((1-Math.min(1,Math.sqrt(nearest)))*255);data[p+2]=Math.round(noise(x/2,y/2,z/2,32)*255);data[p+3]=255;
 }
 const texture=new T.Data3DTexture(data,N,N,N);texture.format=T.RGBAFormat;texture.minFilter=texture.magFilter=T.LinearFilter;texture.wrapS=texture.wrapT=texture.wrapR=T.RepeatWrapping;texture.unpackAlignment=1;texture.needsUpdate=true;return texture;
}
export function createVolumetricClouds(renderer){
 if(!renderer?.isWebGLRenderer)return null;
 const noise=densityTexture(),target=new T.WebGLRenderTarget(1024,512,{type:T.HalfFloatType,depthBuffer:false,stencilBuffer:false});target.texture.wrapS=T.RepeatWrapping;const targets=[target,target.clone()];let front=0;
 const uniforms={origin:{value:new T.Vector3(0,.015,0)},volume:{value:noise},coverage:{value:0},sun:{value:new T.Vector3(0,1,0)},sunTint:{value:new T.Color('white')},day:{value:1},storm:{value:0},offset:{value:new T.Vector2()}};
 const material=new T.ShaderMaterial({glslVersion:T.GLSL3,uniforms,depthTest:false,depthWrite:false,vertexShader:'out vec2 cloudUV;void main(){cloudUV=uv;gl_Position=vec4(position.xy,0.,1.);}',fragmentShader:`
 precision highp float;precision highp sampler3D;in vec2 cloudUV;out vec4 cloudResult;
 uniform sampler3D volume;uniform float coverage,day,storm;uniform vec3 sun,sunTint,origin;uniform vec2 offset;
 float topDistance(vec3 d,float height){float r=6360.+origin.y,b=r*d.y;return -b+sqrt(b*b+pow(6360.+height,2.)-r*r);}
 float density(vec3 p,bool detailed){float altitude=length(p+vec3(0.,6360.,0.))-6360.;float h=(altitude-1.3)/1.8;if(h<=0.||h>=1.)return 0.;
  vec3 uv=vec3((p.x-offset.x)*.14,h*.23,(p.z-offset.y)*.14);vec3 n=texture(volume,uv).rgb;float shape=n.r*.78+n.g*.22;float detail=detailed?texture(volume,uv*3.7+vec3(.13,.21,.07)).g:.65;
  float profile=smoothstep(0.,.12,h)*(1.-smoothstep(.45,1.,h));float threshold=mix(.74,.30,coverage);float body=max(0.,shape-threshold)*5.5;body=max(0.,body-(1.-detail)*.32);return body*profile*smoothstep(0.,.06,coverage);}
 void main(){if(coverage<.0001){cloudResult=vec4(0.);return;}float az=(cloudUV.x-.5)*6.2831853,elevation=cloudUV.y*cloudUV.y*1.5707963;vec3 d=vec3(cos(az)*cos(elevation),sin(elevation),sin(az)*cos(elevation));float start=topDistance(d,1.3),end=min(topDistance(d,3.1),start+35.);float stepSize=(end-start)/32.;float jitter=fract(sin(dot(gl_FragCoord.xy,vec2(12.9898,78.233)))*43758.5453);vec3 color=vec3(0.);float transmittance=1.;float mu=dot(d,sun),forward=.10+.055*(1.-.65*.65)/pow(max(.04,1.+.65*.65-2.*.65*mu),1.5);
 for(int i=0;i<32;i++){vec3 p=origin+d*(start+(float(i)+.2+.6*jitter)*stepSize);float rho=density(p,true);if(rho>.001){float optical=0.;for(int j=0;j<2;j++){float dist=.25+float(j)*.60;optical+=density(p+sun*dist,false)*.60;}float shadow=exp(-optical*5.);float a=1.-exp(-rho*stepSize*4.2);float h=clamp((length(p+vec3(0.,6360.,0.))-6360.-1.3)/1.8,0.,1.);vec3 ambient=mix(vec3(.19,.25,.33),vec3(.52,.60,.69),h)*(.008+.992*day)*(1.-storm*.38);vec3 direct=sunTint*shadow*(.65+forward)*day*(1.-storm*.55);color+=transmittance*a*(ambient+direct);transmittance*=1.-a;if(transmittance<.015)break;}}
 float distanceFade=exp(-start*.025);cloudResult=vec4(color*distanceFade,(1.-transmittance)*distanceFade);}`});
 const scene=new T.Scene(),quad=new T.Mesh(new T.PlaneGeometry(2,2),material),camera=new T.Camera();scene.add(quad);let key='',last=-Infinity;
 return {get texture(){return targets[front].texture;},update(u){const v=[u.cloud.value,u.day.value,u.storm.value,...u.sunPosition.value.toArray(),...u.cloudOffset.value.toArray(),...u.cloudOrigin.value.toArray()].join(',');const now=performance.now();u.cloudBlend.value=Math.min(1,(now-last)/100);if(v===key||now-last<100)return;const first=key==='';key=v;last=now;front=1-front;u.cloudMap.value=targets[front].texture;u.cloudMapPrevious.value=targets[first?front:1-front].texture;u.cloudBlend.value=first?1:0;uniforms.origin.value.copy(u.cloudOrigin.value);uniforms.coverage.value=u.cloud.value;uniforms.sun.value.copy(u.sunPosition.value);uniforms.sunTint.value.copy(u.sunColor.value);uniforms.day.value=u.day.value;uniforms.storm.value=u.storm.value;uniforms.offset.value.copy(u.cloudOffset.value);const previous=renderer.getRenderTarget(),auto=renderer.autoClear;try{renderer.autoClear=true;renderer.setRenderTarget(targets[front]);renderer.render(scene,camera);}finally{renderer.setRenderTarget(previous);renderer.autoClear=auto;}},dispose(){noise.dispose();targets.forEach(t=>t.dispose());quad.geometry.dispose();material.dispose();}};
}
