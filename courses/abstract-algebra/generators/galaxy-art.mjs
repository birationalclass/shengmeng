import * as T from '../../../visuals/3d/vendor/three.module.js';

// Deterministic, volumetric distributions rather than repeated flat spiral lines.
export function stellarField(index,count=7600,extent=10){
 let seed=811+index*173;const rand=()=>{seed=seed*16807%2147483647;return(seed-1)/2147483646;};
 const normal=()=>Math.sqrt(-2*Math.log(Math.max(1e-8,rand())))*Math.cos(6.283185*rand());
 const positions=[],colors=[];
 const palettes=[[0x7296b8,0xdfb792],[0x91b6d3,0xbe94be],[0x7caaa7,0xe0cd9e],[0xb5a1d3,0xe3bda0],[0x869bda,0xbaabc7],[0xb6cadc,0xe0c8a7],[0x8aafd0,0xb79bc4]];
 const low=new T.Color(palettes[index][0]),high=new T.Color(palettes[index][1]);
 for(let i=0;i<count;i++){
  const u=rand(),a=rand()*Math.PI*2;let x,y,z;
  if(index===0){ // A broken, asymmetric nursery with open dark space.
   const side=i%3,centers=[[-3.7,-1.5],[1.1,1.6],[5,-.9]],q=centers[side];
   x=q[0]+normal()*1.9;z=q[1]+normal()*1.05+Math.sin(x*.65)*.65;y=normal()*.55;
  }else if(index===1){ // Two tidal cores with broad, incomplete tails.
   const side=i%2?1:-1,r=Math.pow(u,.7)*5.4,theta=.4+r*.38+normal()*.22;
   x=side*(2.5+Math.cos(theta)*r);z=side*Math.sin(theta)*r*.7;y=normal()*(.18+r*.08);
  }else if(index===2){ // Four stellar associations, no continuous rings.
   const q=[[-4,-2],[-2,3.5],[3,-3],[4,2.4]][i%4];
   x=q[0]+normal()*1.5;z=q[1]+normal()*1.05;y=normal()*.85;
  }else if(index===3){ // A stellar bar and two short, diffuse arms.
   if(u<.4){x=normal()*2.9;z=normal()*.62;y=normal()*.35;}
   else {const s=i%2?1:-1,r=2.3+rand()*5.6,theta=(r-2)*.31+normal()*.17;x=s*(r*Math.cos(theta)+1);z=s*r*Math.sin(theta)*.72;y=normal()*.45;}
  }else if(index===4){ // A braided, inclined filament network.
   x=(u-.5)*16;z=Math.sin(x*.45+(i%3)*1.9)*(1.5+u)+normal()*.72;y=Math.cos(x*.35+i%3)*.8+normal()*.5;
  }else if(index===5){ // A thick elliptical cloud, punctured by a dust lane.
   x=normal()*3.5;z=normal()*2;y=normal()*.95;
   if(Math.abs(z-.32*x)<.45){z+=z>0?.85:-.85;}
  }else { // Rich irregular cluster complex, distinct from a spiral.
   const theta=(i%7)*2.399963,r=2+Math.sqrt((i%7)/6)*4;
   x=Math.cos(theta)*r+normal()*1.35;z=Math.sin(theta)*r+normal()*1.15;y=normal()*.7;
  }
  // Preserve the distinct cloud structures, with diffuse coverage across every orbit.
  if(i%4===0){const r=extent*Math.sqrt(rand()),theta=rand()*Math.PI*2;x=r*Math.cos(theta);z=r*Math.sin(theta);y=normal()*.45;}
  else {const r=Math.hypot(x,z),scaled=extent*Math.tanh(r/7);if(r>0){x*=scaled/r;z*=scaled/r;}}
  positions.push(x,y,z);
  const tint=low.clone().lerp(high,rand());tint.multiplyScalar(.35+rand()*.6);colors.push(tint.r,tint.g,tint.b);
 }
 return {positions,colors};
}

const noiseGLSL=`
float hash(vec3 p){return fract(sin(dot(p,vec3(127.1,311.7,74.7)))*43758.5453);}
float noise(vec3 p){vec3 i=floor(p),f=fract(p);f=f*f*(3.-2.*f);return mix(mix(mix(hash(i),hash(i+vec3(1,0,0)),f.x),mix(hash(i+vec3(0,1,0)),hash(i+vec3(1,1,0)),f.x),f.y),mix(mix(hash(i+vec3(0,0,1)),hash(i+vec3(1,0,1)),f.x),mix(hash(i+vec3(0,1,1)),hash(i+vec3(1,1,1)),f.x),f.y),f.z);}
float fbm(vec3 p){float n=0.,a=.52;for(int i=0;i<5;i++){n+=a*noise(p);p=p*2.07+vec3(3.1,7.4,1.8);a*=.49;}return n;}`;

export function planetMaterial(kind,seed){return new T.ShaderMaterial({uniforms:{kind:{value:kind},seed:{value:seed}},vertexShader:`
 varying vec3 p;varying vec3 n;varying vec3 view;
 void main(){p=position;n=normalize(normalMatrix*normal);vec4 mv=modelViewMatrix*vec4(position,1.);view=normalize(-mv.xyz);gl_Position=projectionMatrix*mv;}`,
 fragmentShader:`varying vec3 p;varying vec3 n;varying vec3 view;uniform float kind;uniform float seed;${noiseGLSL}
 void main(){
  vec3 q=normalize(p),offset=vec3(seed*2.31,seed*.74,seed*1.17);float f=fbm(q*3.2+offset),fine=fbm(q*23.+offset);vec3 c;float water=0.;
  if(kind<.5){
   float land=smoothstep(.49,.53,f);water=1.-land;
   c=mix(vec3(.025,.13,.24),mix(vec3(.13,.23,.17),vec3(.5,.43,.28),smoothstep(.52,.72,f)),land);
   float clouds=smoothstep(.58,.76,fbm(q*5.+offset+fbm(q*3.)*1.6));c=mix(c,vec3(.86,.9,.91),clouds*.87);
   c=mix(c,vec3(.78,.85,.87),smoothstep(.85,.98,abs(q.y)+f*.07));
  }else if(kind<1.5){
   float bands=.5+.5*sin(q.y*29.+fbm(q*5.+offset)*5.);c=mix(vec3(.34,.23,.16),vec3(.81,.68,.48),smoothstep(.13,.85,bands));c=mix(c,vec3(.86,.8,.65),smoothstep(.64,.8,fine)*.4);
  }else if(kind<2.5){c=mix(vec3(.27,.12,.075),vec3(.7,.41,.22),f);c+=fine*.1;c=mix(c,vec3(.8,.69,.49),smoothstep(.62,.8,f));}
  else if(kind<3.5){c=mix(vec3(.16,.32,.4),vec3(.73,.85,.87),smoothstep(.27,.7,f));float cracks=1.-smoothstep(.008,.045,abs(f-.48));c*=1.-cracks*.4;}
  else {c=mix(vec3(.06,.065,.075),vec3(.22,.19,.18),f);float lava=pow(1.-smoothstep(.007,.026,abs(f-.5)),3.);c+=vec3(.6,.08,.006)*lava*.55;}
  vec3 N=normalize(n),L=normalize(vec3(-.65,.6,1.));float lit=max(0.,dot(N,L));float rim=pow(1.-max(0.,dot(N,normalize(view))),3.5);
  float spec=pow(max(0.,dot(reflect(-L,N),normalize(view))),38.)*water*.28;
  vec3 color=c*(.065+lit*.98)+vec3(spec)+vec3(.16,.35,.48)*rim*lit*.32;
  gl_FragColor=vec4(color,1.);
  #include <tonemapping_fragment>
  #include <colorspace_fragment>
 }`});}

export function addPlanetDetails(planet,sphere,kind){
 if(kind===0||kind===3){
  const atmosphere=new T.Mesh(sphere,new T.ShaderMaterial({transparent:true,depthWrite:false,blending:T.AdditiveBlending,vertexShader:`varying vec3 n;varying vec3 v;void main(){vec4 p=modelViewMatrix*vec4(position,1.);n=normalize(normalMatrix*normal);v=normalize(-p.xyz);gl_Position=projectionMatrix*p;}`,fragmentShader:`varying vec3 n;varying vec3 v;void main(){float rim=pow(1.-abs(dot(normalize(n),normalize(v))),4.);float light=max(.1,dot(normalize(n),normalize(vec3(-.65,.6,1.))));gl_FragColor=vec4(.26,.56,.8,rim*light*.22);}`}));
  atmosphere.scale.setScalar(1.025);planet.add(atmosphere);
 }
 if(kind===1){
  const ring=new T.Mesh(new T.RingGeometry(1.35,2.05,96),new T.ShaderMaterial({side:T.DoubleSide,transparent:true,depthWrite:false,vertexShader:`varying vec3 p;void main(){p=position;gl_Position=projectionMatrix*modelViewMatrix*vec4(position,1.);}`,fragmentShader:`varying vec3 p;void main(){float r=length(p.xy);float gap=smoothstep(.015,.045,abs(r-1.73));float a=(.25+.18*sin(r*115.))*gap;gl_FragColor=vec4(.63,.55,.43,a);}`}));ring.rotation.set(-1.1,.22,.25);planet.add(ring);
 }
}
