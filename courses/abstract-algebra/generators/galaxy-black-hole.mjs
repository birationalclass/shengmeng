import * as T from '../../../visuals/3d/vendor/three.module.js';
// S4-sized identity asset. Same gas shading and cached ray method as the approved lab.
const vertex=`varying vec2 uv0;void main(){uv0=uv;gl_Position=vec4(position.xy,0.,1.);}`;
const billboard=`varying vec2 uv0;void main(){uv0=uv;vec4 mv=modelViewMatrix*vec4(0.,0.,0.,1.);vec2 s=vec2(length(modelMatrix[0].xyz),length(modelMatrix[1].xyz));mv.xy+=position.xy*s;gl_Position=projectionMatrix*mv;}`;
const gasShader=`
precision highp float;varying vec2 uv0;uniform vec2 resolution;uniform float time;uniform vec3 eye;uniform float zoom;
float hash(vec3 p){return fract(sin(dot(p,vec3(127.1,311.7,74.7)))*43758.5453);}
float noise(vec3 p){vec3 i=floor(p),f=fract(p);f=f*f*(3.-2.*f);return mix(mix(mix(hash(i),hash(i+vec3(1,0,0)),f.x),mix(hash(i+vec3(0,1,0)),hash(i+vec3(1,1,0)),f.x),f.y),mix(mix(hash(i+vec3(0,0,1)),hash(i+vec3(1,0,1)),f.x),mix(hash(i+vec3(0,1,1)),hash(i+vec3(1,1,1)),f.x),f.y),f.z);}
float fbm(vec3 p){float a=.5,n=0.;for(int k=0;k<4;k++){n+=a*noise(p);p=p*2.07+5.1;a*=.5;}return n;}
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
uniform sampler2D frontMap;uniform sampler2D backMap;uniform vec3 diskU;uniform vec3 diskV;uniform vec3 viewCenter;uniform float modelUnit;uniform mat4 depthProjection;
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
 float shadow=(front.w<-.5||back.w<-.5)?1.:0.;float emission=max(light.r,max(light.g,light.b));float alpha=max(shadow,smoothstep(.015,.32,emission));if(alpha<.01)discard;
 vec4 hit=front.w>.01?front:back;vec3 position=viewCenter;
 if(shadow<.5&&hit.w>.01)position+=(diskU*hit.x+diskV*hit.y)*modelUnit;
 vec4 clip=depthProjection*vec4(position,1.);gl_FragDepth=clamp(.5+.5*clip.z/clip.w,0.,1.);
 gl_FragColor=vec4(light,alpha);
}`;
const rayShader=`
precision highp float;varying vec2 uv0;uniform vec2 resolution;uniform vec3 eye;uniform float zoom;uniform int layer;uniform vec3 diskN;uniform vec3 diskU;uniform vec3 diskV;
vec3 acceleration(vec3 p,float h2){float r2=dot(p,p);return -1.5*h2*p/(r2*r2*sqrt(r2));}
void main(){
 vec2 xy=(uv0-.5)*2.;xy.x*=resolution.x/resolution.y;
 // Rays originate at the actual scene camera, through this asset's world-space footprint.
 vec3 p=eye,v=normalize(vec3(xy*14.85,0.)-eye);
 float b=dot(p,v),d=b*b-dot(p,p)+625.;
 if(d<0.){gl_FragColor=vec4(0.);return;}
 p+=v*max(0.,-b-sqrt(d));
 float h2=dot(cross(p,v),cross(p,v));int hits=0;
 gl_FragColor=vec4(0.);
 for(int i=0;i<240;i++){
  float r=length(p);if(r<1.005){gl_FragColor=vec4(0.,0.,0.,-1.);break;}if(r>55.)break;
  float ds=clamp(r*.065,.025,.8);vec3 old=p,oldV=v;
  vec3 halfV=v+acceleration(p,h2)*ds*.5,halfP=p+v*ds*.5;
  v+=acceleration(halfP,h2)*ds;p+=halfV*ds;
  float before=dot(old,diskN),after=dot(p,diskN);if(before*after<0.){
   float fraction=before/(before-after);vec3 hit=mix(old,p,fraction);float radius=length(hit);
   if(radius>3.&&radius<12.){
    if(hits==layer){vec3 tangent=normalize(cross(hit,diskN));gl_FragColor=vec4(dot(hit,diskU),dot(hit,diskV),dot(tangent,-normalize(mix(oldV,v,fraction))),1.);break;}
    hits++;
   }
  }
 }
}`;
export function galaxyBlackHole(sphere){
 let mapSize=256;
 const targets=[0,1].map(()=>new T.WebGLRenderTarget(256,256,{type:T.HalfFloatType,minFilter:T.NearestFilter,magFilter:T.NearestFilter,depthBuffer:false}));
 const uniforms={resolution:{value:new T.Vector2(256,256)},eye:{value:new T.Vector3(0,0,29)},zoom:{value:1.35*22/(2*.43*29)},time:{value:0},frontMap:{value:targets[0].texture},backMap:{value:targets[1].texture},diskU:{value:new T.Vector3()},diskV:{value:new T.Vector3()},viewCenter:{value:new T.Vector3()},modelUnit:{value:1},depthProjection:{value:new T.Matrix4()}};
 const material=new T.ShaderMaterial({uniforms,vertexShader:billboard,fragmentShader:gasShader,transparent:true,depthWrite:true});
 const body=new T.Mesh(sphere,new T.MeshBasicMaterial({colorWrite:false,depthWrite:false}));
 const image=new T.Mesh(new T.PlaneGeometry(8.5*1.35,8.5*1.35),material);body.add(image);
 const ru={...uniforms,layer:{value:0},diskN:{value:new T.Vector3()},diskU:{value:new T.Vector3()},diskV:{value:new T.Vector3()}};
 const rm=new T.ShaderMaterial({uniforms:ru,vertexShader:vertex,fragmentShader:rayShader});
 const cacheScene=new T.Scene(),cacheCamera=new T.Camera();cacheScene.add(new T.Mesh(new T.PlaneGeometry(2,2),rm));
 const mv=new T.Matrix4(),lastN=new T.Vector3(9,9,9),lastU=new T.Vector3(9,9,9),lastEye=new T.Vector3(999,999,999);
 body.userData.effects=[material];
 body.userData.updateBlackHole=(renderer,camera)=>{
  mv.multiplyMatrices(camera.matrixWorldInverse,body.matrixWorld);
  ru.diskN.value.set(0,1,0).transformDirection(mv);ru.diskU.value.set(1,0,0).transformDirection(mv);ru.diskV.value.set(0,0,1).transformDirection(mv);
  const projected=11.475*new T.Vector3().setFromMatrixScale(body.matrixWorld).x*renderer.domElement.height*camera.projectionMatrix.elements[5]/(2*Math.abs(mv.elements[14]));
  const size=Math.max(128,Math.min(768,Math.ceil(projected/128)*128));
  if(size!==mapSize){mapSize=size;targets.forEach(t=>t.setSize(size,size));ru.resolution.value.set(size,size);lastEye.set(999,999,999);}
  const unit=new T.Vector3().setFromMatrixScale(body.matrixWorld).x*(8.5/22);
  uniforms.diskU.value.copy(ru.diskU.value);uniforms.diskV.value.copy(ru.diskV.value);uniforms.viewCenter.value.setFromMatrixPosition(mv);uniforms.modelUnit.value=unit;uniforms.depthProjection.value.copy(camera.projectionMatrix);
  ru.eye.value.setFromMatrixPosition(mv).multiplyScalar(-1/unit);
  if(lastEye.distanceToSquared(ru.eye.value)<.0001&&lastN.distanceToSquared(ru.diskN.value)<1e-6&&lastU.distanceToSquared(ru.diskU.value)<1e-6)return;
  const previous=renderer.getRenderTarget();for(let i=0;i<2;i++){ru.layer.value=i;renderer.setRenderTarget(targets[i]);renderer.render(cacheScene,cacheCamera);}renderer.setRenderTarget(previous);
  lastEye.copy(ru.eye.value);lastN.copy(ru.diskN.value);lastU.copy(ru.diskU.value);
 };
 return body;
}
