// Reference-sheet art direction: broad cloudy arms, broken dust lanes and embedded stars.
export const GALAXY_PATTERNS={C4:0,V4:1,S3:2,D4:3,Q8:4,S4:5,F56:6,A5:7,S5:8};
export const NEBULA_PROFILES=[
 [2,1.35,.12,.2],[4,.95,.2,.35],[3,1.65,.05,.8],[2,1.25,.72,.28],[4,1.8,.28,.4],[5,1.2,.1,.25],[3,1.05,.46,.75],[2,1.7,.65,.85],[5,1.48,.18,.5]
];
export function dustField(key,count,inner,outer){
 const id=GALAXY_PATTERNS[key],[arms,twist,bar,magenta]=NEBULA_PROFILES[id];let seed=177+id*83;const rand=()=>{seed=seed*16807%2147483647;return(seed-1)/2147483646;},positions=[],colors=[];
 for(let i=0;i<count;i++){const u=Math.pow(rand(),.78),r=inner+(outer-inner)*u,unit=r/outer;let a=(i%arms)*Math.PI*2/arms+twist*Math.log(unit+.12)+Math.sqrt(-2*Math.log(Math.max(.00001,rand())))*Math.cos(rand()*Math.PI*2)*(.16+u*.24);if(i%7===0)a=rand()*Math.PI*2;
 if(key==='S5'){const arm=i%3;a=[.15,2.35,4.6][arm]+u*[1.7,.95,.65][arm]+(rand()-.5)*(.25+.5*u);}
 const height=(rand()+rand()+rand()-1.5)*outer*.025*Math.sin(Math.PI*u);positions.push(r*Math.cos(a),height,r*Math.sin(a));const warm=1-u,light=.25+rand()*.5;colors.push((.46+warm*.45+magenta*.1)*light,(.62+warm*.16-magenta*.08)*light,(.94-warm*.34)*light);}
 return {positions,colors};
}
export function addNebula(T,root,key,inner,outer){
 const id=GALAXY_PATTERNS[key],profile=NEBULA_PROFILES[id],geometry=new T.PlaneGeometry(outer*2,outer*2);geometry.rotateX(-Math.PI/2);
 const material=new T.ShaderMaterial({transparent:true,side:T.DoubleSide,depthWrite:false,blending:T.AdditiveBlending,uniforms:{inner:{value:inner/outer},profile:{value:new T.Vector4(...profile)},seed:{value:id*13.7},opacity:{value:.8}},vertexShader:`varying vec2 q;void main(){q=uv*2.-1.;gl_Position=projectionMatrix*modelViewMatrix*vec4(position,1.);}`,fragmentShader:`precision highp float;varying vec2 q;uniform float inner;uniform vec4 profile;uniform float seed;uniform float opacity;
 float hash(vec2 p){return fract(sin(dot(p,vec2(127.1,311.7))+seed)*43758.5453);}float noise(vec2 p){vec2 i=floor(p),f=fract(p);f=f*f*(3.-2.*f);return mix(mix(hash(i),hash(i+vec2(1,0)),f.x),mix(hash(i+vec2(0,1)),hash(i+vec2(1,1)),f.x),f.y);}float fbm(vec2 p){return .57*noise(p)+.28*noise(p*2.07+7.)+.15*noise(p*4.13+17.);}
 void main(){float r=length(q);if(r<inner||r>1.)discard;float a=atan(-q.y,q.x),cloud=fbm(q*13.),fine=fbm(q*48.),phase=profile.x*(a-profile.y*log(r+.12));float arms=pow(.5+.5*cos(phase+(cloud-.5)*2.7),3.);float taper=smoothstep(inner,inner+.035,r)*(1.-smoothstep(.7,1.,r));float lane=smoothstep(.24,.64,fbm(q*24.+vec2(cos(phase),sin(phase))*.35));float clumps=smoothstep(.3,.8,cloud);float density=(.12+arms*.88)*(.3+clumps*1.8)*(.18+.82*lane)*taper;density*=.7+.3*sin(a+seed);
 vec3 warm=vec3(.82,.62,.39),cool=mix(vec3(.28,.53,.85),vec3(.68,.23,.77),profile.w);vec3 color=mix(warm,cool,smoothstep(inner,.85,r));color=mix(color,vec3(.85,.91,1.),smoothstep(.61,.87,fine)*.65);gl_FragColor=vec4(color,density*opacity*.6);}`});
 const cloud=new T.Mesh(geometry,material);root.add(cloud);return cloud;
}
export function inflowSample(age,inner,outer,lane=0){
 const u=Math.max(0,Math.min(1,age)),r=outer+(inner*.085-outer)*Math.pow(u,1.3),a=lane+u*u*6.8;
 return {x:Math.cos(a)*r,y:0,z:Math.sin(a)*r,r,angle:a};
}
export function nearDustCopies(field,inner,outer,count=220){
 const pool=[];for(let i=0;i<field.positions.length;i+=3){const r=Math.hypot(field.positions[i],field.positions[i+2]);if(r>=inner&&r<=inner+(outer-inner)*.28)pool.push(i);}
 if(!pool.length)return {positions:[],colors:[],tails:[],heights:[]};
 const positions=[],colors=[],tails=[],heights=[];
 for(let i=0;i<count;i++){const j=pool[(i*137)%pool.length],phase=((i*618033)%1000000)/1000000;for(let tail=0;tail<6;tail++){positions.push(field.positions[j],phase,field.positions[j+2]);colors.push(field.colors[j],field.colors[j+1],field.colors[j+2]);tails.push(tail);heights.push(field.positions[j+1]);}}
 return {positions,colors,tails,heights};
}
export function addInflow(T,root,field,inner,outer,count=220){
 const copies=nearDustCopies(field,inner,outer,count),geometry=new T.BufferGeometry();geometry.setAttribute('position',new T.Float32BufferAttribute(copies.positions,3));geometry.setAttribute('color',new T.Float32BufferAttribute(copies.colors,3));geometry.setAttribute('tail',new T.Float32BufferAttribute(copies.tails,1));geometry.setAttribute('originHeight',new T.Float32BufferAttribute(copies.heights,1));
 const material=new T.ShaderMaterial({vertexColors:true,transparent:true,depthWrite:false,blending:T.AdditiveBlending,uniforms:{time:{value:0},inner:{value:inner*.085},opacity:{value:.8}},vertexShader:`uniform float time;uniform float inner;attribute float tail;attribute float originHeight;varying float light;varying vec3 tint;void main(){float age=fract(position.y+time/9.);float u=max(0.,age-tail*.008);float startRadius=length(position.xz);float r=mix(startRadius,inner,pow(u,1.3));float a=atan(position.z,position.x)+u*u*6.8;vec4 p=modelViewMatrix*vec4(r*cos(a),originHeight*(1.-u),r*sin(a),1.);light=smoothstep(0.,.06,age)*(1.-smoothstep(.96,1.,age))*exp(-tail*.35);tint=mix(color,vec3(.8,.9,1.),u*.65);gl_PointSize=clamp((tail<.5?1.8:1.2)*100./max(1.,-p.z),1.,4.);gl_Position=projectionMatrix*p;}`,fragmentShader:`uniform float opacity;varying float light;varying vec3 tint;void main(){float d=length(gl_PointCoord-.5)*2.;if(d>1.)discard;float a=pow(1.-d,1.7)*light*opacity;gl_FragColor=vec4(tint,a);}`});
 const points=new T.Points(geometry,material);points.frustumCulled=false;root.add(points);return points;
}
