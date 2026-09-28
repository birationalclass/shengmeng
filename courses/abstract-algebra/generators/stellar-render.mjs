import * as T from '../../../visuals/3d/vendor/three.module.js';

const billboard=`varying vec2 vUv;void main(){vUv=uv;vec4 mv=modelViewMatrix*vec4(0.,0.,0.,1.);vec2 s=vec2(length(modelMatrix[0].xyz),length(modelMatrix[1].xyz));mv.xy+=position.xy*s;gl_Position=projectionMatrix*mv;}`;
const diskVertex=billboard.replace('varying vec2 vUv;', 'varying vec2 vUv;varying vec3 diskNormal;varying vec3 diskU;varying vec3 diskV;').replace('vUv=uv;', 'vUv=uv;diskNormal=normalize(mat3(modelViewMatrix)*vec3(0.,1.,0.));diskU=normalize(mat3(modelViewMatrix)*vec3(1.,0.,0.));diskV=normalize(mat3(modelViewMatrix)*vec3(0.,0.,1.));');
const noise=`float hash(vec3 p){return fract(sin(dot(p,vec3(127.1,311.7,74.7)))*43758.5453);}float noise(vec3 p){vec3 i=floor(p),f=fract(p);f=f*f*(3.-2.*f);return mix(mix(mix(hash(i),hash(i+vec3(1,0,0)),f.x),mix(hash(i+vec3(0,1,0)),hash(i+vec3(1,1,0)),f.x),f.y),mix(mix(hash(i+vec3(0,0,1)),hash(i+vec3(1,0,1)),f.x),mix(hash(i+vec3(0,1,1)),hash(i+vec3(1,1,1)),f.x),f.y),f.z);}float fbm(vec3 p){float n=0.,a=.5;for(int i=0;i<5;i++){n+=noise(p)*a;p=p*2.03+7.17;a*=.5;}return n;}`;

export function blackHole(sphere){
 const body=new T.Mesh(sphere,new T.MeshBasicMaterial({colorWrite:false,depthWrite:false}));
 // Null-ray orbital acceleration for a nonrotating unit Schwarzschild radius.
 // Finite integration budget and an artistic thin disk: a real-time approximation.
 const material=new T.ShaderMaterial({transparent:true,depthWrite:false,depthTest:false,uniforms:{time:{value:0}},vertexShader:diskVertex,fragmentShader:`
 varying vec2 vUv;varying vec3 diskNormal;varying vec3 diskU;varying vec3 diskV;uniform float time;${noise}
 vec3 disk(vec3 p,vec3 normal){
  float r=length(p);vec3 tangent=normalize(cross(normal,p));float beam=clamp(pow(1./(1.-dot(tangent,vec3(0,0,1))*.34),3.),.35,2.8);
  float a=atan(dot(p,normalize(diskV)),dot(p,normalize(diskU))),flow=a-time*.32/pow(max(r/3.,1.),1.5);
  float turbulent=fbm(vec3(r*2.,cos(flow)*4.,sin(flow)*4.));
  float filaments=.48+.25*turbulent+.10*sin(r*19.+turbulent*9.+flow*2.);
  float heat=pow(3./max(3.,r),.75);vec3 c=mix(vec3(.7,.12,.025),vec3(1.,.84,.51),heat*heat);
  float fall=smoothstep(3.,3.45,r)*(1.-smoothstep(7.,10.,r));return c*filaments*fall*beam*1.8;
 }
 void main(){
  vec2 screen=(vUv-.5)*22.;vec3 p=vec3(0.,0.,20.),v=normalize(vec3(screen,-20.));
  float h2=dot(cross(p,v),cross(p,v)),alpha=0.;vec3 color=vec3(0.);vec3 normal=normalize(diskNormal);bool captured=false;
  for(int j=0;j<160;j++){
   float r=length(p);if(r<1.02){captured=true;break;}if(r>26.)break;
   float ds=clamp(r*.085,.055,.65);vec3 old=p;float before=dot(p,normal);
   vec3 accel=-1.5*h2*p/pow(r,5.);v+=accel*ds;p+=v*ds;
   float after=dot(p,normal);
   if(before*after<0.){vec3 hit=mix(old,p,before/(before-after));float radius=length(hit);
    if(radius>3.&&radius<10.){vec3 emission=disk(hit,normal);float opacity=.8*smoothstep(3.,3.6,radius)*(1.-smoothstep(6.,10.,radius)); color+=(1.-alpha)*emission*opacity;alpha+=(1.-alpha)*opacity;}
   }
  }
  if(captured)alpha=1.;
  float b=sqrt(h2),photon=exp(-pow((b-2.598)*48.,2.));color+=vec3(1.,.64,.27)*photon*.32;alpha=max(alpha,photon*.6);
  color=vec3(1.)-exp(-color*1.2);gl_FragColor=vec4(color,alpha);
 }`});
 const image=new T.Mesh(new T.PlaneGeometry(8.5,8.5),material);image.renderOrder=12;body.add(image);body.userData.effects=[material];return body;
}

export function detailedStar(sphere,rank,seed){
 const tint=new T.Color(rank.type==='blue-star'?0xaed7ff:rank.type==='gold-star'?0xffc35f:0xff693a);
 const material=new T.ShaderMaterial({uniforms:{time:{value:0},seed:{value:seed},tint:{value:tint}},vertexShader:`varying vec3 p;varying vec3 n;varying vec3 view;void main(){p=position;n=normalize(normalMatrix*normal);vec4 mv=modelViewMatrix*vec4(position,1.);view=normalize(-mv.xyz);gl_Position=projectionMatrix*mv;}`,fragmentShader:`varying vec3 p;varying vec3 n;varying vec3 view;uniform float time;uniform float seed;uniform vec3 tint;${noise}
 void main(){vec3 q=normalize(p),shift=vec3(seed*2.3,time*.017,seed*.7);float broad=fbm(q*5.+shift);float cells=noise(q*72.+fbm(q*12.+shift)*2.7+shift);float lanes=smoothstep(.24,.56,cells);float fine=noise(q*165.+shift);
  float activity=fbm(q*8.+shift);float umbra=smoothstep(.70,.79,activity);float penumbra=smoothstep(.64,.72,activity);
  float mu=max(0.,dot(normalize(n),normalize(view))),limb=.24+.76*pow(mu,.58);
  vec3 color=mix(tint*.32,tint*1.32+vec3(.1),.4+lanes*.55);color*=.82+fine*.23;color*=1.-penumbra*.38;color*=1.-umbra*.88;color*=limb;
  gl_FragColor=vec4(color,1.);
  #include <colorspace_fragment>
 }`});
 const body=new T.Mesh(sphere,material);
 const coronaMat=new T.ShaderMaterial({transparent:true,depthWrite:false,blending:T.AdditiveBlending,uniforms:{time:{value:0},seed:{value:seed},tint:{value:tint}},vertexShader:billboard,fragmentShader:`varying vec2 vUv;uniform float time;uniform float seed;uniform vec3 tint;${noise}
 void main(){vec2 q=(vUv-.5)*5.;float r=length(q);if(r<.985)discard;float a=atan(q.y,q.x);float drift=a+.055*sin(time*.65+seed)+time*.035;
  vec3 p=vec3(cos(drift)*6.,sin(drift)*6.,time*.32+seed);float fil=fbm(p);
  float pulse=.5+.5*sin(time*1.65+a*5.+seed*2.+fil*5.);
  float reach=.13+pow(fil,2.4)*(1.05+pulse*.85);
  float outward=.68+.32*sin((r-1.)*17.-time*3.8+a*3.+fil*6.);
  float ray=exp(-(r-1.)/reach)*(.14+fil*.55)*(.65+pulse*.55)*outward;float edge=exp(-pow((r-1.025)*45.,2.))*.3;
  float loop=0.;
  float opacity=(ray+edge+loop)*(1.-smoothstep(1.6,2.4,r));gl_FragColor=vec4(tint,opacity);
 }`});
 body.add(new T.Mesh(new T.PlaneGeometry(5,5),coronaMat));body.userData.effects=[material,coronaMat];
 // Three-dimensional magnetic arches rooted at two photospheric footpoints.
 for(let j=0;j<4;j++){
  const angle=seed*.9+j*1.7,normal=new T.Vector3(Math.cos(angle),Math.sin(angle),.35*Math.sin(seed+j)).normalize();
  const tangent=new T.Vector3(-normal.y,normal.x,0).normalize(),points=[];
  for(let k=0;k<=32;k++){const u=k/32;points.push(normal.clone().multiplyScalar(.975+Math.sin(u*Math.PI)*(.12+j*.025)).addScaledVector(tangent,(u-.5)*.32));}
  const arch=new T.Mesh(new T.TubeGeometry(new T.CatmullRomCurve3(points),32,.006,5,false),new T.MeshBasicMaterial({color:tint,transparent:true,opacity:.7,blending:T.AdditiveBlending,depthWrite:false}));
  body.add(arch);
 }
 return body;
}
