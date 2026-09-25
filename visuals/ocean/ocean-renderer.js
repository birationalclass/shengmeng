import * as THREE from '../3d/vendor/three.module.js';
import { makeWaveSpectrum } from './wave-spectrum.js?v=20260925-ocean-4';

const environment = `
uniform float uTime, uWave, uWind, uSun;
const float PI=3.14159265359;
float sat(float x){return clamp(x,0.,1.);}
float hash(vec2 p){vec3 q=fract(vec3(p.xyx)*.1031);q+=dot(q,q.yzx+33.33);return fract((q.x+q.y)*q.z);}
float noise(vec2 p){vec2 i=floor(p),f=fract(p);f=f*f*(3.-2.*f);return mix(mix(hash(i),hash(i+vec2(1,0)),f.x),mix(hash(i+vec2(0,1)),hash(i+1.),f.x),f.y);}
float fbm(vec2 p){float a=.5,v=0.;mat2 m=mat2(1.62,1.17,-1.17,1.62);for(int i=0;i<5;i++){v+=a*noise(p);p=m*p+7.3;a*=.5;}return v;}
vec3 bubbleCell(vec2 p){
 vec2 cell=floor(p),f=fract(p),nearest=vec2(0.);float d=10.;
 for(int y=-1;y<=1;y++)for(int x=-1;x<=1;x++){
  vec2 q=vec2(float(x),float(y));
  vec2 r=q+vec2(hash(cell+q),hash(cell+q+17.3))-f;
  float h=dot(r,r);if(h<d){d=h;nearest=r;}
 }
 return vec3(nearest,sqrt(d));
}
vec3 sunDirection(){float a=uSun*PI/180.;return normalize(vec3(-.08,sin(a),-cos(a)));}
vec3 sky(vec3 rd,bool clouds){
 float day=smoothstep(5.,22.,uSun),dusk=1.-smoothstep(-3.,3.,uSun),y=max(rd.y,0.);
 vec3 sd=sunDirection();float focus=pow(max(0.,dot(rd,sd)),9.);
 vec3 zenith=mix(vec3(.105,.17,.29),vec3(.12,.37,.65),day);zenith=mix(zenith,vec3(.045,.065,.19),dusk);
 vec3 horizon=mix(vec3(.48,.39,.35),vec3(.62,.82,.91),day);horizon=mix(horizon,vec3(.34,.25,.34),dusk);
 horizon+=vec3(.60,.19,.025)*focus*(1.-day)*(1.-dusk*.65);
 vec3 col=mix(horizon,zenith,pow(sat(y),.45));
 vec3 warm=mix(vec3(1.2,.55,.15),vec3(.8,.91,1.),day);
 col+=warm*pow(focus,3.)*.22*(1.-day*.65);
 col+=mix(vec3(1.,.55,.15),vec3(.5,.62,.69),day)*exp(-pow(length(rd-sd)/.15,1.2))*.85*(1.-dusk*.6);
 if(clouds)col+=vec3(5.,3.75,1.85)*(1.-smoothstep(.009,.012,length(rd-sd)))*(1.-dusk*.7);
 if(clouds&&rd.y>0.){
  vec2 cp=rd.xz/(rd.y+.14)*1.6+vec2(uTime*.004,0.);
  float n=fbm(cp*1.35+vec2(16.7,3.)),w=fbm(cp*vec2(.9,3.5)+21.);
  float density=smoothstep(.41,.68,n*.82+w*.18)*smoothstep(0.,.07,rd.y)*.90;
  vec3 dark=mix(vec3(.065,.10,.17),vec3(.51,.64,.73),day);dark=mix(dark,vec3(.10,.10,.23),dusk);
  vec3 light=mix(vec3(1.05,.41,.15),vec3(1.,1.01,1.02),day);light=mix(light,vec3(.43,.27,.40),dusk);
  col=mix(col,mix(light,dark,smoothstep(.07,.9,sat((n-.37)*6.5)))+warm*focus*.15,density);
 }
 return col;
}
vec3 tone(vec3 x){x*=.95;return pow(clamp((x*(2.51*x+.03))/(x*(2.43*x+.59)+.14),0.,1.),vec3(.82));}
`;

// Coordinates follow the coast: cross-shore C points inland, A follows the
// shoreline. The moving profile is sampled in material coordinates, so a
// single sheet of triangles can fold over and expose the inside of the lip.
const surfaceModel = `
uniform sampler2D uProfile;
uniform vec4 uWaves[32];
uniform vec2 uPhases[32];
float shore(float a){return 3.4+1.4*sin(a*.023)+.38*sin(a*.093);}
vec2 worldXZ(vec2 ca){return vec2(.94*ca.x+.341174*ca.y,.341174*ca.x-.94*ca.y);}
float phaseOffset(float a){return 2.8*sin(a*.067)+1.25*sin(a*.19)+.32*sin(a*.57);}
float beachHeight(vec2 ca){return (ca.x-shore(ca.y))*.055+.012*noise(ca*.7);}
float swashReach(float a){
 float p=(uTime*2.05-phaseOffset(a)-shore(a)+1.)*.3141593;
 float pulse=clamp(.5+.5*cos(p)+.12*sin(2.*p),0.,1.);
 return -.7+3.6*pulse+.23*sin(a*.67)+.09*sin(a*1.73);
}
float swashLevel(vec2 ca){
 float edge=shore(ca.y)+swashReach(ca.y);
 return max(0.,beachHeight(ca))+.085*smoothstep(-.15,2.8,edge-ca.x);
}
vec4 profileAt(vec2 ca){
 float moving=uTime*2.05;
 float q=ca.x-moving+phaseOffset(ca.y);
 float id=floor((q+10.)/20.);
 float local=mod(q+10.,20.)-10.-(hash(vec2(id,17.))-.5)*3.;
 float center=ca.x-local;
 float bar=2.6*sin(ca.y*.13+id*1.7)+1.5*noise(vec2(ca.y*.31,id));
 float stage=clamp((center-(shore(ca.y)-27.+bar))/24.,0.,1.);
 vec4 result=texture2D(uProfile,vec2(clamp((local+10.)/20.,0.,1.),stage));
 float breakingPatch=smoothstep(.24,.78,noise(vec2(ca.y*.12,id*2.7)));
 // Most of the front spills; only short sections develop an overhanging lip.
 float smoothRidge=exp(-pow((local+.4)/3.0,2.))*.60;
 float spill=1.-smoothstep(.68,.96,stage);
 result.r*=(.25+.75*breakingPatch)*(1.-smoothstep(.74,1.,stage));
 result.g=mix(smoothRidge*spill,result.g,.35+.65*breakingPatch);
 result.g*=.65+.65*hash(vec2(id,29.));
 result.b=max(result.b,smoothstep(.36,.60,stage)*(1.-smoothstep(.85,1.,stage))*exp(-pow((local-1.)/2.3,2.)))*(.45+breakingPatch*.55);
 result*=smoothstep(-60.,-18.,center);
 return result;
}
vec3 surfaceAt(vec2 ca){
 vec4 profile=profileAt(ca);
 float d=(shore(ca.y)-ca.x)*.12;
 float heightScale=uWave*.42*(.75+.40*noise(vec2(ca.y*.18,4.)));
 float offshore=smoothstep(3.,10.,shore(ca.y)-ca.x);
 vec2 displaced=ca+vec2(profile.r*offshore,0.);
 vec3 p=vec3(worldXZ(displaced).x,profile.g*heightScale,worldXZ(displaced).y);
 p.y+=(noise(vec2(ca.y*1.3+uTime*1.1,ca.x*.9))- .5)*.075*profile.b;
 float calm=smoothstep(.1,5.,d)*(1.-profile.a*.75);
 vec2 base=worldXZ(ca);
 for(int i=0;i<32;i++){
  vec4 w=uWaves[i];float phase=dot(base,w.xy)*w.z-uPhases[i].x*uTime+uPhases[i].y;
  float wavelength=6.2831853/w.z;
  float resolved=1.-smoothstep(wavelength*7.+25.,wavelength*24.+85.,length(base-cameraPosition.xz));
  float amp=w.w*(.4+uWind*.6)*uWave*calm*resolved;
  p.xz+=w.xy*amp*.56*cos(phase);p.y+=amp*sin(phase);
 }
 // A shallow swash tongue advances and recedes after the broken front.
 float wet=smoothstep(-.3,1.8,d);
 p.y=p.y*wet+swashLevel(ca)*(1.-smoothstep(.2,1.8,d));
 return p;
}
`;

// Whitewater has its own displaced surface. The same continuous density drives
// its height, coverage and shadow, so foam islands taper into the water instead
// of being cut from a uniformly raised sheet.
const whitewaterModel = `
uniform sampler2D uFoam;
float foamDensity(vec2 ca){
 vec2 uv=(ca-vec2(-35.,-45.))/vec2(60.,160.);
 float history=0.;
 if(all(greaterThan(uv,vec2(0.)))&&all(lessThan(uv,vec2(1.))))history=texture2D(uFoam,uv).r;
 float fresh=profileAt(ca).b;
 float edge=shore(ca.y)+swashReach(ca.y)-ca.x;
 float rim=exp(-pow((edge-.25)/.37,2.))*smoothstep(-2.,1.,ca.x-shore(ca.y));
 return max(history,max(fresh*.85,rim*.68))*smoothstep(-.12,.4,edge);
}
float foamLumps(vec2 ca){
 vec2 flow=ca-vec2(uTime*.65,.16*sin(uTime*.3));
 float large=noise(flow*.85+vec2(noise(flow*.32))*2.);
 float cells=noise(flow*2.1);
 return smoothstep(.29,.68,large*.72+cells*.28);
}
float foamThickness(vec2 ca){
 float density=foamDensity(ca),lumps=foamLumps(ca);
 float fresh=profileAt(ca).b;
 float rim=exp(-pow((shore(ca.y)+swashReach(ca.y)-ca.x-.3)/.5,2.));
 float h=(.015+fresh*(.16+.06*uWave)+rim*.045)*smoothstep(.08,.55,density)*lumps;
 return h;
}
vec3 whitewaterAt(vec2 ca){
 vec3 p=surfaceAt(ca);
 p.y+=foamThickness(ca)+.002;
 return p;
}
`;

function cubic(a, b, c, d, t) {
  const v = 1 - t;
  return [v*v*v*a[0]+3*v*v*t*b[0]+3*v*t*t*c[0]+t*t*t*d[0], v*v*v*a[1]+3*v*v*t*b[1]+3*v*t*t*c[1]+t*t*t*d[1]];
}
function smooth(a, b, x) { const t = Math.max(0, Math.min(1, (x-a)/(b-a))); return t*t*(3-2*t); }
const mix = (a,b,t) => a+(b-a)*t;

// Original authored cross-sections, inspired by the deformation-map workflow
// described by Guerrilla at SIGGRAPH 2022. Each key has four cubic segments,
// including the upper lip AND its underside. No self-crossing Gerstner loops.
const profiles = [
  {t:0, points:[[-10,0],[-7,0],[-4,.25],[-2,.50],[-.7,.66],[.8,.62],[1.5,.45],[1.8,.38],[2.2,.29],[3,.19],[5,.03],[8,0],[10,0]]},
  {t:.30, points:[[-10,0],[-7,0],[-4,.40],[-2,.75],[-.7,1.05],[.6,1.03],[1.1,.82],[1.4,.59],[1.6,.3],[2,.16],[4,0],[8,0],[10,0]]},
  {t:.50, points:[[-10,0],[-6,0],[-3,.65],[-.85,1.12],[.15,1.38],[1.1,1.27],[1.4,1.04],[1.30,.84],[.62,.93],[.32,.67],[.10,.15],[3.0,0],[10,0]]},
  {t:.63, points:[[-10,0],[-6,0],[-2.6,.77],[-.65,1.20],[.80,1.61],[2.3,1.27],[2.2,.75],[2.0,.47],[.42,1.02],[.30,.65],[.15,.08],[3.2,0],[10,0]]},
  {t:.73, points:[[-10,0],[-6,0],[-2.6,.57],[-.55,.89],[1.2,1.24],[3.0,.70],[3.2,.40],[2.5,.24],[.72,.70],[.62,.49],[.28,.02],[4,0],[10,0]]},
  {t:.84, points:[[-10,0],[-5,0],[-1.5,.32],[.3,.40],[2,.43],[3.2,.37],[3.7,.24],[3.9,.15],[4.1,.10],[4.5,.07],[6,0],[8,0],[10,0]]},
  {t:1, points:[[-10,0],[-7,0],[-4,.025],[-1,.04],[1,.05],[2,.04],[3,.03],[3.5,.02],[4,.01],[4.5,0],[6,0],[8,0],[10,0]]}
];
function makeProfileTexture() {
  const width=512, height=160, data=new Float32Array(width*height*4);
  // Unequal parameter intervals put geometry into the lip instead of wasting
  // most of the longitudinal vertices on the nearly flat tail.
  const breaks=[0,.34,.51,.69,1];
  for(let j=0;j<height;j++) {
    const stage=j/(height-1);
    let key=0;while(key<profiles.length-2 && stage>profiles[key+1].t)key++;
    const a=profiles[key],b=profiles[key+1],blend=smooth(a.t,b.t,stage);
    const points=a.points.map((p,i)=>[mix(p[0],b.points[i][0],blend),mix(p[1],b.points[i][1],blend)]);
    for(let i=0;i<width;i++) {
      const u=i/(width-1);let segment=0;while(segment<3&&u>breaks[segment+1])segment++;
      const s=(u-breaks[segment])/(breaks[segment+1]-breaks[segment]);
      const v=cubic(...points.slice(segment*3,segment*3+4),s);
      const lip=smooth(.39,.48,u)*(1-smooth(.57,.65,u));
      const collapse=smooth(.70,.86,stage)*smooth(.26,.5,u)*(1-smooth(.75,.92,u))*.7;
      const foam=smooth(.46,.69,stage)*(1-smooth(.9,1,stage))*Math.max(lip,collapse);
      const k=(j*width+i)*4;
      data[k]=v[0]-(u*20-10);data[k+1]=v[1];data[k+2]=foam;data[k+3]=smooth(.15,.46,u)*(1-smooth(.75,1,u));
    }
  }
  const halfData=new Uint16Array(data.length);
  for(let i=0;i<data.length;i++)halfData[i]=THREE.DataUtils.toHalfFloat(data[i]);
  const texture=new THREE.DataTexture(halfData,width,height,THREE.RGBAFormat,THREE.HalfFloatType);
  texture.minFilter=texture.magFilter=THREE.LinearFilter;texture.needsUpdate=true;
  return texture;
}

function makeSeaGeometry(columns=640,rows=440) {
  const vertices=new Float32Array((columns+1)*(rows+1)*3),indices=new Uint32Array(columns*rows*6);
  for(let j=0;j<=rows;j++) {
    const v=j/rows;
    const along=v<.72 ? -45+v/.72*160 : 115+(Math.exp((v-.72)/.28*5.2)-1)*17;
    for(let i=0;i<=columns;i++) {
      const u=i/columns;
      const cross=u<.34 ? -35-(Math.exp((.34-u)/.34*5.2)-1)*13 : -35+(u-.34)/.66*60;
      const k=(j*(columns+1)+i)*3;vertices[k]=cross;vertices[k+1]=0;vertices[k+2]=along;
    }
  }
  let k=0;for(let j=0;j<rows;j++)for(let i=0;i<columns;i++){
    const a=j*(columns+1)+i,b=a+1,c=a+columns+1,d=c+1;
    indices[k++]=a;indices[k++]=b;indices[k++]=c;indices[k++]=b;indices[k++]=d;indices[k++]=c;
  }
  const geometry=new THREE.BufferGeometry();geometry.setAttribute('position',new THREE.BufferAttribute(vertices,3));geometry.setIndex(new THREE.BufferAttribute(indices,1));
  return geometry;
}

function makeWhitewaterGeometry(low=false) {
  const geometry=new THREE.PlaneGeometry(60,160,low?180:400,low?280:640);
  geometry.rotateX(-Math.PI/2);geometry.translate(-5,0,35);
  return geometry;
}

function waveSpectrum(wind=.45) {
  const components=makeWaveSpectrum(wind);
  return {
    waves:components.map(c=>new THREE.Vector4(c.x,c.z,c.k,c.amplitude)),
    phases:components.map(c=>new THREE.Vector2(c.omega,c.phase))
  };
}

export class OceanRenderer {
  constructor(canvas) {
    this.canvas=canvas;
    this.renderer=new THREE.WebGLRenderer({canvas,antialias:true,alpha:false,powerPreference:'high-performance'});
    if(!this.renderer.extensions.has('EXT_color_buffer_float'))throw new Error('Floating-point render targets are required for whitewater transport.');
    this.renderer.setPixelRatio(1);this.renderer.setClearColor(0x142b3a);this.renderer.autoClear=false;
    this.renderer.debug.onShaderError=(context,program,vertex,fragment)=>{throw new Error(context.getShaderInfoLog(vertex)+'\n'+context.getShaderInfoLog(fragment));};
    this.scene=new THREE.Scene();this.camera=new THREE.PerspectiveCamera(56,1,.1,6500);
    const spectrum=waveSpectrum();
    this.uniforms={uTime:{value:5.6},uWave:{value:1.2},uWind:{value:.45},uSun:{value:5},uProfile:{value:makeProfileTexture()},uWaves:{value:spectrum.waves},uPhases:{value:spectrum.phases},uFoam:{value:null},uViewportHeight:{value:960}};
    this.lastTime=null;this.meshQuality='fine';this.spectrumWind=.45;
    this.setupSky();this.setupWater();this.setupBeach();this.setupFoam();this.setupWhitewater();this.setupFroth();this.setupSpray();
  }
  setupSky() {
    const material=new THREE.ShaderMaterial({uniforms:this.uniforms,depthWrite:false,depthTest:false,side:THREE.BackSide,
      vertexShader:'varying vec3 vRay;void main(){vec4 p=modelMatrix*vec4(position,1.);vRay=p.xyz-cameraPosition;gl_Position=projectionMatrix*viewMatrix*p;}',
      fragmentShader:environment+'varying vec3 vRay;void main(){gl_FragColor=vec4(tone(sky(normalize(vRay),true)),1.);}' });
    const mesh=new THREE.Mesh(new THREE.SphereGeometry(5200,24,12),material);mesh.renderOrder=-10;mesh.frustumCulled=false;this.scene.add(mesh);
  }
  setupWater() {
    this.seaGeometry=makeSeaGeometry();
    const material=new THREE.ShaderMaterial({uniforms:this.uniforms,side:THREE.DoubleSide,transparent:true,depthWrite:true,forceSinglePass:true,
      vertexShader:environment+surfaceModel+`
       varying vec3 vWorld,vNormal;varying vec2 vCA;varying vec4 vProfile;
       void main(){vec2 ca=position.xz;vec3 p=surfaceAt(ca);vec3 dc=surfaceAt(ca+vec2(.035,0.))-surfaceAt(ca-vec2(.035,0.));vec3 da=surfaceAt(ca+vec2(0.,.08))-surfaceAt(ca-vec2(0.,.08));vNormal=normalize(cross(dc,da));vWorld=p;vCA=ca;vProfile=profileAt(ca);gl_Position=projectionMatrix*viewMatrix*vec4(p,1.);}`,
      fragmentShader:environment+surfaceModel+`
       uniform sampler2D uFoam;
       varying vec3 vWorld,vNormal;varying vec2 vCA;varying vec4 vProfile;
       void main(){
        float coast=shore(vCA.y);float depth=(coast-vCA.x)*.18;
        vec3 view=normalize(cameraPosition-vWorld);float distance=length(cameraPosition-vWorld);
        float waterThickness=vWorld.y-beachHeight(vCA);
        float edge=coast+swashReach(vCA.y)-vCA.x;
        float coverage=smoothstep(-.12,.35,edge)*smoothstep(0.,.023,waterThickness);
        if(coverage<.005)discard;
        vec3 n=normalize(vNormal);if(!gl_FrontFacing)n=-n;
        vec2 uv=vWorld.xz;
        vec2 slope=vec2(.86,.51)*cos(dot(uv,vec2(2.9,1.7))-uTime*3.7);
        slope+=vec2(.96,-.28)*cos(dot(uv,vec2(6.1,-1.8))-uTime*5.4)*.48;
        slope+=vec2(.71,.71)*cos(dot(uv,vec2(11.1,11.1))-uTime*8.1)*.20;
        float detail=(.010+uWind*.023)*exp(-distance*.025)*(1.-vProfile.a*.45);
        n=normalize(n+vec3(-slope.x,0.,-slope.y)*detail);
        vec3 sd=sunDirection(),r=reflect(-view,n);float reflectedHorizon=smoothstep(-.12,.06,r.y);r.y=max(.002,r.y);
        float day=smoothstep(5.,22.,uSun),dusk=1.-smoothstep(-3.,3.,uSun);
        float fresnel=.0204+.9796*pow(1.-sat(dot(view,n)),5.);
        vec3 reflected=sky(r,true);
        vec3 deep=mix(vec3(.008,.042,.052),vec3(.012,.105,.145),day);
        vec3 shallow=mix(vec3(.025,.092,.09),vec3(.035,.24,.22),day);
        vec3 body=mix(shallow,deep,smoothstep(0.,5.,depth));
        float backlit=pow(sat(dot(view,sd)),3.);float thin=sat(vWorld.y/(uWave*.9));
        body+=vec3(.025,.13,.095)*thin*(.25+backlit*.75)*(1.-dusk*.45);
        vec3 sand=mix(vec3(.19,.14,.10),vec3(.43,.34,.22),day);
        body=mix(sand,body,1.-exp(-max(0.,waterThickness)*2.8));
        body*=.6+.4*sat(n.y);
        float underLip=1.-smoothstep(-.10,.30,vNormal.y);
        vec3 reflection=mix(reflected,mix(body*.35,reflected,reflectedHorizon),underLip);
        vec3 col=mix(body,reflection,fresnel*.87);
        vec3 halfV=normalize(sd+view);float nh=max(.001,dot(n,halfV));
        float rough=.065+uWind*.048,a2=pow(rough,4.),den=nh*nh*(a2-1.)+1.;
        float spec=a2/(PI*den*den);float sf=.02+.98*pow(1.-sat(dot(view,halfV)),5.);
        vec3 light=mix(vec3(1.8,.91,.36),vec3(1.4,1.4,1.25),day)*(1.-dusk*.55);
        col+=light*min(14.,spec*sf*.24)*smoothstep(-4.,1.,uSun);
        // Persistent advected whitewater. Breakup contains several bubble
        // scales; no single repeated Voronoi cell or painted crest stripe.
        vec2 foamUV=(vCA-vec2(-35.,-45.))/vec2(60.,160.);
        float foam=0.;if(all(greaterThan(foamUV,vec2(0.)))&&all(lessThan(foamUV,vec2(1.))))foam=texture2D(uFoam,foamUV).r;
        foam=max(foam,vProfile.b*.70);
        vec2 flow=vec2(vCA.x-uTime*.52,vCA.y+sin(vCA.x*.3)*.7);
        float turbulence=fbm(flow*2.1+fbm(flow*.45)*2.);
        float tiny=noise(flow*37.);
        float strands=abs(noise(flow*5.3)-.5);
        float rim=exp(-max(0.,edge)*5.)*smoothstep(-1.3,.5,vCA.x-coast);
        foam=max(foam,rim*.8);
        float bubbles=(1.-smoothstep(.08,.22,strands))*.22;
        float foamPattern=smoothstep(.40,.61,turbulence+foam*.10+bubbles);
        foam=smoothstep(.05,.70,foam)*mix(foamPattern,.57,smoothstep(30.,150.,distance));
        vec3 white=mix(vec3(.64,.67,.65),vec3(.98,1.04,1.02),day);white=mix(white,vec3(.24,.33,.46),dusk);white*=(.88+.12*sat(dot(n,sd)))*(.84+tiny*.16);
        // Thin residual bubbles remain in the water material; fresh aerated
        // water is drawn by the separate whitewater geometry above this mesh.
        col=mix(col,white,foam*.40);
        // Water under the curling lip is shaded; the exposed thin rim glows.
        float cavity=smoothstep(.38,.72,vProfile.a)*smoothstep(.25,.8,vProfile.g)*(1.-sat(n.y))*.20;
        col*=(1.-cavity)*mix(.78,1.,smoothstep(-.30,.10,vNormal.y));
        float fog=1.-exp(-distance*.00065);col=mix(col,sky(normalize(vec3(-view.x,.005,-view.z)),false),min(.94,fog));
        gl_FragColor=vec4(tone(col),coverage);
       }`});
    this.water=new THREE.Mesh(this.seaGeometry,material);this.water.frustumCulled=false;this.scene.add(this.water);
  }
  setupBeach() {
    const geometry=this.seaGeometry;
    const material=new THREE.ShaderMaterial({uniforms:this.uniforms,side:THREE.DoubleSide,
      vertexShader:environment+surfaceModel+`varying vec3 vWorld;varying vec2 vCA;void main(){vec2 ca=position.xz;vec2 xz=worldXZ(ca);vWorld=vec3(xz.x,beachHeight(ca),xz.y);vCA=ca;gl_Position=projectionMatrix*viewMatrix*vec4(vWorld,1.);}`,
      fragmentShader:environment+surfaceModel+`
       uniform sampler2D uFoam;varying vec3 vWorld;varying vec2 vCA;
       void main(){
        float d=vCA.x-shore(vCA.y),day=smoothstep(5.,22.,uSun);
        float grain=noise(vCA*180.);
        vec3 col=mix(vec3(.31,.23,.17),vec3(.57,.46,.33),day)*(.93+grain*.10);
        vec2 uv=(vCA-vec2(-35.,-45.))/vec2(60.,160.);
        float history=0.;if(all(greaterThan(uv,vec2(0.)))&&all(lessThan(uv,vec2(1.))))history=texture2D(uFoam,uv).g;
        float wet=max(history,1.-smoothstep(-.6,2.,d));
        float channels=sin(vCA.y*7.+noise(vCA*.8)*5.)*.5+.5;
        col*=.96+.04*channels;
        float detail=exp(-length(cameraPosition-vWorld)*.055);
        float g0=noise(vCA*28.);
        vec2 grad=vec2(noise(vCA*28.+vec2(.06,0.))-g0,noise(vCA*28.+vec2(0.,.06))-g0);
        vec2 gradWorld=worldXZ(grad);
        vec3 view=normalize(cameraPosition-vWorld),n=normalize(vec3(-.052-gradWorld.x*.24*detail,1.,-.019-gradWorld.y*.24*detail));
        vec3 r=reflect(-view,n);
        col=mix(col,col*.44+sky(r,true)*.16,wet);
        col+=vec3(1.,.63,.32)*pow(sat(dot(r,sunDirection())),360.)*wet;
        float distance=length(vWorld-cameraPosition);
        col=mix(col,sky(normalize(vec3(-view.x,.005,-view.z)),false),min(.9,1.-exp(-distance*.00065)));
        gl_FragColor=vec4(tone(col),1.);
       }`});
    const beach=new THREE.Mesh(geometry,material);beach.frustumCulled=false;this.beach=beach;this.scene.add(beach);
  }
  setupFoam() {
    const options={type:THREE.HalfFloatType,format:THREE.RGBAFormat,minFilter:THREE.LinearFilter,magFilter:THREE.LinearFilter,depthBuffer:false};
    this.foamA=new THREE.WebGLRenderTarget(768,768,options);this.foamB=this.foamA.clone();
    this.foamUniforms={...this.uniforms,uPrevious:{value:this.foamA.texture},uDt:{value:1/60}};
    this.foamScene=new THREE.Scene();this.foamCamera=new THREE.OrthographicCamera(-1,1,1,-1,0,1);
    const material=new THREE.ShaderMaterial({uniforms:this.foamUniforms,depthTest:false,depthWrite:false,
      vertexShader:'varying vec2 vUv;void main(){vUv=uv;gl_Position=vec4(position.xy,0.,1.);}',
      fragmentShader:environment+surfaceModel+`
       uniform sampler2D uPrevious;uniform float uDt;varying vec2 vUv;
       void main(){
        vec2 ca=vUv*vec2(60.,160.)+vec2(-35.,-45.);
        float d=shore(ca.y)-ca.x;
        float swashPhase=(uTime*2.05-phaseOffset(ca.y)-shore(ca.y)+1.)*.3141593;
        float runup=-sin(swashPhase)*1.5;
        vec2 velocity=vec2(mix(runup,1.8,smoothstep(0.,9.,d)),.36*sin(ca.x*.45+uTime*.3));
        velocity+=vec2(sin(ca.y*.7+uTime),cos(ca.x*.8-uTime))*.22;
        vec2 previous=vUv-velocity*uDt/vec2(60.,160.);
        float old=texture2D(uPrevious,previous).r*exp(-uDt*.27);
        vec4 profile=profileAt(ca);
        float source=profile.b*(.35+noise(ca*1.7+uTime*.05)*.65)*smoothstep(-.5,.5,d);
        float edge=d+swashReach(ca.y);
        source+=exp(-abs(edge)*4.)*smoothstep(-.3,1.,runup)*.32;
        float foam=old+source*uDt*1.7;
        foam*=exp(-uDt*max(0.,-edge)*3.);
        float wet=max(texture2D(uPrevious,vUv).g*exp(-uDt*.026),smoothstep(-.25,.35,edge));
        gl_FragColor=vec4(min(1.,foam),wet,0.,1.);
       }`});
    this.foamScene.add(new THREE.Mesh(new THREE.PlaneGeometry(2,2),material));
    this.renderer.setClearColor(0x000000);
    this.renderer.setRenderTarget(this.foamA);this.renderer.clearColor();this.renderer.setRenderTarget(this.foamB);this.renderer.clearColor();this.renderer.setRenderTarget(null);
    this.renderer.setClearColor(0x142b3a);
    this.uniforms.uFoam.value=this.foamA.texture;
  }
  setupSpray() {
    const count=11000,values=new Float32Array(count*3);
    for(let i=0;i<count;i++){values[i*3]=(Math.sin(i*127.1)*43758.5453)%1;values[i*3]=Math.abs(values[i*3]);values[i*3+1]=Math.abs((Math.sin(i*311.7)*27182.818)%1);values[i*3+2]=Math.abs((Math.sin(i*74.7)*31415.92)%1);}
    const geo=new THREE.BufferGeometry();geo.setAttribute('position',new THREE.BufferAttribute(values,3));
    const material=new THREE.ShaderMaterial({uniforms:this.uniforms,transparent:true,depthWrite:false,blending:THREE.NormalBlending,
      vertexShader:environment+surfaceModel+`varying float vAlpha;void main(){float along=-35.+position.x*140.;float cross=shore(along)-11.;float period=20./2.05;float phase=mod((uTime-(cross+phaseOffset(along))/2.05),period);float age=phase-position.y*.8;float alive=step(0.,age)*(1.-step(.8,age));age=max(0.,age);vec2 ca=vec2(cross+1.8+age*(1.4+position.z*1.6),along+(position.z-.5)*age*1.4);vec2 xz=worldXZ(ca);float y=uWave*(.32+position.y*.10)+age*(.4+position.z*1.2)-4.9*age*age;vec3 p=vec3(xz.x,max(.02,y),xz.y);vec4 mv=viewMatrix*vec4(p,1.);gl_Position=projectionMatrix*mv;gl_PointSize=clamp((16.+position.z*18.)/max(1.,-mv.z),.6,2.5);vAlpha=alive*smoothstep(0.,.10,age)*(1.-smoothstep(.25,.8,age))*.25*step(.03,y);}`,
      fragmentShader:environment+`varying float vAlpha;void main(){float d=length(gl_PointCoord-.5);if(d>.5||vAlpha<.01)discard;float day=smoothstep(5.,22.,uSun);vec3 c=mix(vec3(.95,.72,.44),vec3(.86,.98,1.),day);gl_FragColor=vec4(c,vAlpha*(1.-smoothstep(.2,.5,d)));}`});
    const spray=new THREE.Points(geo,material);spray.frustumCulled=false;spray.renderOrder=4;this.scene.add(spray);
  }
  setupWhitewater() {
    const geometry=makeWhitewaterGeometry();
    const material=new THREE.ShaderMaterial({uniforms:this.uniforms,side:THREE.DoubleSide,transparent:true,depthWrite:false,forceSinglePass:true,
      vertexShader:environment+surfaceModel+whitewaterModel+`
       varying vec3 vWorld,vNormal;varying vec2 vCA;varying float vThickness;
       void main(){
        vec2 ca=position.xz;vec3 p=whitewaterAt(ca);
        vec3 dc=whitewaterAt(ca+vec2(.055,0.))-whitewaterAt(ca-vec2(.055,0.));
        vec3 da=whitewaterAt(ca+vec2(0.,.075))-whitewaterAt(ca-vec2(0.,.075));
        vNormal=normalize(cross(dc,da));vWorld=p;vCA=ca;vThickness=foamThickness(ca);
        gl_Position=projectionMatrix*viewMatrix*vec4(p,1.);
       }`,
      fragmentShader:environment+surfaceModel+whitewaterModel+`
       varying vec3 vWorld,vNormal;varying vec2 vCA;varying float vThickness;
       void main(){
        float density=foamDensity(vCA),lumps=foamLumps(vCA);
        float depth=vWorld.y-beachHeight(vCA);
        float edge=shore(vCA.y)+swashReach(vCA.y)-vCA.x;
        float opacity=smoothstep(.06,.52,density)*smoothstep(.05,.50,lumps);
        opacity*=smoothstep(-.08,.28,edge)*smoothstep(0.,.035,depth);
        if(opacity<.015)discard;
        vec3 n=normalize(vNormal);if(n.y<0.)n=-n;
        vec2 fuv=vCA-vec2(uTime*.65,0.);
        float fine=noise(fuv*59.);
        float micro=noise(fuv*11.);
        vec2 microSlope=vec2(noise(fuv*11.+vec2(.08,0.))-micro,noise(fuv*11.+vec2(0.,.08))-micro);
        n=normalize(n+vec3(-microSlope.x,.0,-microSlope.y)*1.8);
        vec3 bubble=bubbleCell(fuv*110.);
        float resolved=1.-smoothstep(.35,1.3,length(fwidth(fuv*110.)));
        float bubbleCap=sqrt(max(.02,1.-dot(bubble.xy,bubble.xy)*3.));
        vec2 bubbleSlope=worldXZ(bubble.xy);
        n=normalize(n+vec3(bubbleSlope.x,.0,bubbleSlope.y)*resolved*.5);
        float day=smoothstep(5.,22.,uSun),dusk=1.-smoothstep(-3.,3.,uSun);
        vec3 ambient=mix(vec3(.44,.49,.54),vec3(.67,.77,.82),day);
        vec3 direct=mix(vec3(.48,.32,.17),vec3(.48,.46,.39),day);
        float diffuse=max(0.,dot(n,sunDirection()));
        float selfShade=.64+.36*smoothstep(.01,.16,vThickness);
        vec3 col=(ambient+direct*diffuse)*selfShade*(.83+.17*micro);
        col=mix(col,vec3(.22,.29,.39),dusk*.7);
        col*=mix(1.,.76+.24*bubbleCap,resolved)*(.93+.07*fine);
        float dist=length(cameraPosition-vWorld);
        col=mix(col,sky(normalize(vWorld-cameraPosition),false),min(.7,1.-exp(-dist*.00065)));
        gl_FragColor=vec4(tone(col),opacity);
       }`});
    this.whitewater=new THREE.Mesh(geometry,material);this.whitewater.frustumCulled=false;this.whitewater.renderOrder=2;this.scene.add(this.whitewater);
  }
  setupFroth() {
    const count=48000,values=new Float32Array(count*3);
    for(let i=0;i<count;i++){
      values[i*3]=((i*.61803398875)%1);
      values[i*3+1]=((i*.7548776662)%1);
      values[i*3+2]=((i*.569840291)%1);
    }
    const geometry=new THREE.BufferGeometry();geometry.setAttribute('position',new THREE.BufferAttribute(values,3));
    const material=new THREE.ShaderMaterial({uniforms:this.uniforms,transparent:true,depthWrite:true,
      vertexShader:environment+surfaceModel+whitewaterModel+`
       uniform float uViewportHeight;varying vec3 vCenterView;varying float vRadius,vOpacity;
       void main(){
        float along=-22.+position.x*115.;
        float moving=uTime*2.05;
        float id=floor((shore(along)-12.-moving+phaseOffset(along)+10.)/20.);
        float center=moving-phaseOffset(along)+id*20.+(hash(vec2(id,17.))-.5)*3.;
        vec2 ca=vec2(center-2.3+position.y*6.5,along);
        vec4 wave=profileAt(ca);
        vec3 p=whitewaterAt(ca);
        vRadius=(.006+.016*position.z*position.z)*pow(uWave,.3);
        p.y+=vRadius*.35;
        vec4 mv=viewMatrix*vec4(p,1.);vCenterView=mv.xyz;
        gl_Position=projectionMatrix*mv;
        gl_PointSize=clamp(vRadius*uViewportHeight*projectionMatrix[1][1]/max(.1,-mv.z),.1,50.);
        vOpacity=smoothstep(.18,.50,wave.b)*smoothstep(.04,.5,foamLumps(ca))*(1.-smoothstep(25.,65.,-mv.z))*.65;
        vOpacity*=smoothstep(.45,1.8,gl_PointSize);
       }`,
      fragmentShader:environment+`
       uniform mat4 projectionMatrix;
       varying vec3 vCenterView;varying float vRadius,vOpacity;
       void main(){
        vec2 xy=gl_PointCoord*2.-1.;xy.y=-xy.y;
        float r2=dot(xy,xy);if(r2>.94||vOpacity<.04)discard;
        vec3 sphereN=vec3(xy,sqrt(1.-r2));
        vec3 n=normalize(vec3(dot(viewMatrix[0].xyz,sphereN),dot(viewMatrix[1].xyz,sphereN),dot(viewMatrix[2].xyz,sphereN)));
        vec3 positionView=vCenterView+sphereN*vRadius;
        vec4 clip=projectionMatrix*vec4(positionView,1.);
        gl_FragDepth=clip.z/clip.w*.5+.5;
        float day=smoothstep(5.,22.,uSun),dusk=1.-smoothstep(-3.,3.,uSun);
        vec3 ambient=mix(vec3(.47,.53,.57),vec3(.74,.81,.85),day);
        vec3 sunlight=mix(vec3(.40,.28,.14),vec3(.38,.37,.32),day);
        vec3 col=(ambient+sunlight*max(0.,dot(n,sunDirection())))*(.83+.17*sphereN.z);
        col=mix(col,vec3(.22,.30,.41),dusk*.7);
        gl_FragColor=vec4(tone(col),vOpacity*(1.-smoothstep(.68,.94,r2)));
       }`});
    this.froth=new THREE.Points(geometry,material);this.froth.frustumCulled=false;this.froth.renderOrder=3;this.scene.add(this.froth);
  }
  resize(width,height){this.renderer.setSize(width,height,false);this.uniforms.uViewportHeight.value=height;this.camera.aspect=width/height;this.camera.updateProjectionMatrix();}
  draw(state) {
    if(state.wind!==this.spectrumWind){
      const spectrum=waveSpectrum(state.wind);this.uniforms.uWaves.value=spectrum.waves;this.uniforms.uPhases.value=spectrum.phases;this.spectrumWind=state.wind;
    }
    const meshQuality=state.quality==='low'||state.scale<.55?'low':'fine';
    if(meshQuality!==this.meshQuality){
      const previous=this.seaGeometry;this.seaGeometry=meshQuality==='low'?makeSeaGeometry(320,240):makeSeaGeometry();
      this.water.geometry=this.beach.geometry=this.seaGeometry;previous.dispose();this.meshQuality=meshQuality;
      this.whitewater.geometry.dispose();this.whitewater.geometry=makeWhitewaterGeometry(meshQuality==='low');
    }
    this.uniforms.uTime.value=state.time;this.uniforms.uWave.value=state.wave;this.uniforms.uWind.value=state.wind;this.uniforms.uSun.value=state.sun;
    const mobile=1-smooth(.6,1.1,this.camera.aspect);
    const yaw=state.yaw-mobile*.10-.22;
    this.camera.position.set(6.8-mobile*1.8,2.5+state.distance,7.5);
    this.camera.lookAt(this.camera.position.x+Math.sin(yaw)*30,this.camera.position.y+Math.sin(-.115+state.pitch)*30,this.camera.position.z-Math.cos(yaw)*30);
    if(this.lastTime===null){
      for(let i=0;i<96;i++){
        this.uniforms.uTime.value=state.time-7.68+i*.08;this.foamUniforms.uDt.value=.08;this.foamUniforms.uPrevious.value=this.foamA.texture;
        this.renderer.setRenderTarget(this.foamB);this.renderer.render(this.foamScene,this.foamCamera);
        [this.foamA,this.foamB]=[this.foamB,this.foamA];
      }
      this.renderer.setRenderTarget(null);this.uniforms.uTime.value=state.time;this.uniforms.uFoam.value=this.foamA.texture;
    }
    const dt=this.lastTime===null ? .016 : Math.max(0,Math.min(2,state.time-this.lastTime));
    if(dt>0 || this.lastTime===null){
      const steps=Math.max(1,Math.ceil(dt/.04));
      for(let i=0;i<steps;i++){
        this.uniforms.uTime.value=state.time-dt+dt*(i+1)/steps;
        this.foamUniforms.uDt.value=dt/steps;this.foamUniforms.uPrevious.value=this.foamA.texture;
        this.renderer.setRenderTarget(this.foamB);this.renderer.render(this.foamScene,this.foamCamera);
        [this.foamA,this.foamB]=[this.foamB,this.foamA];
      }
      this.renderer.setRenderTarget(null);this.uniforms.uFoam.value=this.foamA.texture;this.uniforms.uTime.value=state.time;
    }
    this.lastTime=state.time;
    this.renderer.clear();this.renderer.render(this.scene,this.camera);
  }
  isContextLost(){return this.renderer.getContext().isContextLost();}
}

export { makeProfileTexture, profiles as waveProfiles };
export const modelGLSL = { environment, surfaceModel, whitewaterModel };
