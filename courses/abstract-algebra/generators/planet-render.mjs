import * as T from '../../../visuals/3d/vendor/three.module.js';
const noise=`float hash(vec3 p){return fract(sin(dot(p,vec3(127.1,311.7,74.7)))*43758.5453);}float noise(vec3 p){vec3 i=floor(p),f=fract(p);f=f*f*(3.-2.*f);return mix(mix(mix(hash(i),hash(i+vec3(1,0,0)),f.x),mix(hash(i+vec3(0,1,0)),hash(i+vec3(1,1,0)),f.x),f.y),mix(mix(hash(i+vec3(0,0,1)),hash(i+vec3(1,0,1)),f.x),mix(hash(i+vec3(0,1,1)),hash(i+vec3(1,1,1)),f.x),f.y),f.z);}float fbm(vec3 p){float n=0.,a=.5;for(int i=0;i<5;i++){n+=noise(p)*a;p=p*2.03+7.17;a*=.5;}return n;}`;
const vertex=`varying vec3 q;varying vec3 N;varying vec3 world;void main(){q=position;N=normalize(mat3(modelMatrix)*normal);world=(modelMatrix*vec4(position,1.)).xyz;gl_Position=projectionMatrix*viewMatrix*vec4(world,1.);}`;
export function detailedPlanet(sphere,kind,seed){
 const uniforms={time:{value:0},seed:{value:seed},kind:{value:kind===3?1:kind},ringed:{value:kind===3?1:0},center:{value:new T.Vector3()},radius:{value:1},host:{value:new T.Vector3(-6,3,5)}};
 const material=new T.ShaderMaterial({uniforms,vertexShader:vertex,fragmentShader:`
 varying vec3 q;varying vec3 N;varying vec3 world;uniform float time;uniform float seed;uniform float kind;uniform vec3 host;${noise}
 void main(){vec3 p=normalize(q),o=vec3(seed*2.31,seed*.74,seed*1.17);float f=fbm(p*3.8+o),fine=fbm(p*38.+o);vec3 color;float water=0.;
 if(kind<.5){float land=smoothstep(.48,.515,f);water=1.-land;vec3 ground=mix(vec3(.045,.14,.065),vec3(.38,.26,.10),smoothstep(.51,.7,f));ground*=.75+fine*.6;color=mix(vec3(.009,.065,.15),ground,land);color=mix(color,vec3(.78,.85,.86),smoothstep(.86,.96,abs(p.y)+f*.12));}
 else if(kind<1.5){float latitude=asin(p.y),longitude=atan(p.z,p.x),wind=time*(.02+.04*sin(latitude*12.));vec3 flow=vec3(cos(longitude+wind),latitude,sin(longitude+wind));float turbulence=fbm(flow*9.+o);float band=.5+.5*sin(latitude*37.+turbulence*4.);color=mix(vec3(.24,.095,.035),vec3(.85,.66,.39),smoothstep(.05,.85,band));float d=length(vec2((longitude-.6)*cos(latitude),(latitude+.27)*1.8));float spiral=sin(atan(latitude+.27,longitude-.6)*3.-d*45.+time*.15+turbulence*3.);color=mix(color,vec3(.52,.12,.045)*(.8+spiral*.15),1.-smoothstep(.12,.26,d));color*=.8+fine*.45;}
 else{float ridge=abs(fbm(p*9.+o)-.49);float cracks=1.-smoothstep(.009,.025,ridge);color=mix(vec3(.2,.38,.46),vec3(.76,.87,.9),smoothstep(.25,.7,f));color*=.8+fine*.3;color=mix(color,vec3(.04,.13,.2),cracks*.8);}
 vec3 n=normalize(N),L=normalize(host-world),V=normalize(cameraPosition-world);float light=max(0.,dot(n,L));float spec=pow(max(0.,dot(n,normalize(L+V))),95.)*water;
 color=color*(.025+light*1.25)+vec3(.6,.75,.9)*spec*.65;
 gl_FragColor=vec4(color,1.);
 #include <colorspace_fragment>
 }`});
 const body=new T.Mesh(sphere,material);const effects=[material];
 if(kind===0){const cloudMat=new T.ShaderMaterial({uniforms,vertexShader:vertex,transparent:true,depthWrite:false,fragmentShader:`varying vec3 q;varying vec3 N;varying vec3 world;uniform float time;uniform float seed;uniform vec3 host;${noise}void main(){vec3 p=normalize(q);float a=time*.026; p=vec3(cos(a)*p.x-sin(a)*p.z,p.y,sin(a)*p.x+cos(a)*p.z);float cloud=fbm(p*7.+vec3(seed,0,0)+fbm(p*4.)*2.);float opacity=smoothstep(.52,.7,cloud)*.85;float lit=max(0.,dot(normalize(N),normalize(host-world)));gl_FragColor=vec4(vec3(.78,.85,.9)*(.04+lit),opacity);}`});const cloud=new T.Mesh(sphere,cloudMat);cloud.scale.setScalar(1.017);body.add(cloud);}
 const atmosphere=new T.Mesh(sphere,new T.ShaderMaterial({uniforms,vertexShader:vertex,side:T.BackSide,transparent:true,depthWrite:false,blending:T.AdditiveBlending,fragmentShader:`varying vec3 N;varying vec3 world;uniform vec3 host;void main(){vec3 n=normalize(N),v=normalize(cameraPosition-world);float rim=pow(1.-abs(dot(n,v)),3.5);float lit=smoothstep(-.25,.7,dot(n,normalize(host-world)));gl_FragColor=vec4(.20,.48,.84,rim*lit*.23);}`}));atmosphere.scale.setScalar(1.055);body.add(atmosphere);
 if(kind===3){
  const rings=new T.Mesh(new T.RingGeometry(1.28,2.25,160),new T.ShaderMaterial({uniforms,vertexShader:vertex,side:T.DoubleSide,transparent:true,depthWrite:false,fragmentShader:`
  varying vec3 q;varying vec3 N;varying vec3 world;uniform vec3 host;uniform vec3 center;uniform float radius;
  void main(){float r=length(q.xy);float bands=.6+.16*sin(r*170.)+.12*sin(r*391.);float cassini=smoothstep(.025,.06,abs(r-1.87));float encke=smoothstep(.004,.014,abs(r-2.13));float opacity=bands*cassini*encke*smoothstep(1.28,1.39,r)*(1.-smoothstep(2.19,2.25,r));opacity*=mix(.3,.85,smoothstep(1.5,1.59,r));
   vec3 L=normalize(host-world),toCenter=center-world;float along=dot(toCenter,L);float miss=sqrt(max(0.,dot(toCenter,toCenter)-along*along))/radius;float shadow=along>0.?smoothstep(.88,1.06,miss):1.;float lit=.22+.78*abs(dot(normalize(N),L));vec3 color=mix(vec3(.36,.29,.21),vec3(.82,.74,.57),bands)*lit*(.07+.93*shadow);gl_FragColor=vec4(color,opacity);
   #include <colorspace_fragment>
  }`}));rings.rotation.x=-Math.PI/2;body.add(rings);body.rotation.z=.46;body.userData.spinBasePlanet=body.quaternion.clone();
  const scale=new T.Vector3();body.onBeforeRender=()=>{body.getWorldPosition(uniforms.center.value);body.getWorldScale(scale);uniforms.radius.value=scale.x;};
 }
 body.userData.effects=effects;body.userData.hostLight=uniforms.host;return body;
}
