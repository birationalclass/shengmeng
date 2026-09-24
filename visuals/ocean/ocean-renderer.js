import * as THREE from '../3d/vendor/three.module.js';

const environment = `
uniform float uTime, uWave, uWind, uSun;
const float PI=3.14159265359;
float sat(float x){return clamp(x,0.,1.);}
float hash(vec2 p){vec3 q=fract(vec3(p.xyx)*.1031);q+=dot(q,q.yzx+33.33);return fract((q.x+q.y)*q.z);}
float noise(vec2 p){vec2 i=floor(p),f=fract(p);f=f*f*(3.-2.*f);return mix(mix(hash(i),hash(i+vec2(1,0)),f.x),mix(hash(i+vec2(0,1)),hash(i+1.),f.x),f.y);}
float fbm(vec2 p){float a=.5,v=0.;mat2 m=mat2(1.62,1.17,-1.17,1.62);for(int i=0;i<5;i++){v+=a*noise(p);p=m*p+7.3;a*=.5;}return v;}
vec3 sunDirection(){float a=uSun*PI/180.;return normalize(vec3(-.08,sin(a),-cos(a)));}
vec3 sky(vec3 rd,bool clouds){
 float day=smoothstep(5.,22.,uSun),dusk=1.-smoothstep(-3.,3.,uSun),y=max(rd.y,0.);
 vec3 sd=sunDirection();float focus=pow(max(0.,dot(rd,sd)),9.);
 vec3 zenith=mix(vec3(.075,.13,.23),vec3(.12,.37,.65),day);zenith=mix(zenith,vec3(.045,.065,.19),dusk);
 vec3 horizon=mix(vec3(1.02,.31,.08),vec3(.62,.82,.91),day);horizon=mix(horizon,vec3(.42,.21,.30),dusk);
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
uniform vec4 uWaves[18];
uniform vec2 uPhases[18];
float shore(float a){return 3.4+.65*sin(a*.028)+.18*sin(a*.081);}
vec2 worldXZ(vec2 ca){return vec2(.94*ca.x+.341174*ca.y,.341174*ca.x-.94*ca.y);}
float phaseOffset(float a){return 2.4*sin(a*.035)+.8*sin(a*.115)+.40*(noise(vec2(a*.61,1.))-.5);}
vec4 profileAt(vec2 ca){
 float moving=uTime*2.35;
 float q=ca.x-moving+phaseOffset(ca.y);
 float local=mod(q+10.,20.)-10.;
 float center=ca.x-local;
 float stage=clamp((center-(shore(ca.y)-21.))/23.,0.,1.);
 vec4 result=texture2D(uProfile,vec2((local+10.)/20.,stage));
 result*=smoothstep(-60.,-18.,center);
 return result;
}
vec3 surfaceAt(vec2 ca){
 vec4 profile=profileAt(ca);
 float d=(shore(ca.y)-ca.x)*.18;
 float heightScale=uWave*.64*(.82+.32*noise(vec2(ca.y*.23,4.)));
 vec2 displaced=ca+vec2(profile.r,0.);
 vec3 p=vec3(worldXZ(displaced).x,profile.g*heightScale,worldXZ(displaced).y);
 p.y+=(noise(vec2(ca.y*1.8+uTime*.6,ca.x*1.7))-.5)*.13*profile.b;
 float calm=smoothstep(.1,5.,d)*(1.-profile.a*.75);
 vec2 base=worldXZ(ca);
 for(int i=0;i<18;i++){
  vec4 w=uWaves[i];float phase=dot(base,w.xy)*w.z-uPhases[i].x*uTime+uPhases[i].y;
  float amp=w.w*(.4+uWind*.6)*uWave*calm;
  p.xz+=w.xy*amp*.56*cos(phase);p.y+=amp*sin(phase);
 }
 // A shallow swash tongue advances and recedes after the broken front.
 float wet=smoothstep(-.55,.55,d);
 p.y=(p.y+.14*(.5+.5*sin(uTime*.74+ca.y*.06))*exp(-abs(d)*2.))*wet;
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

function waveSpectrum() {
  // A deterministic directional spectrum: no tiled displacement texture and
  // no row of identical sine ridges. Long swells and short wind waves coexist.
  const waves=[],phases=[];
  for(let i=0;i<18;i++) {
    const wavelength=34*Math.pow(.828,i), k=2*Math.PI/wavelength;
    const angle=-.31+Math.sin(i*2.399)*(.35+i*.022);
    const amplitude=.15*Math.pow(.79,i)*(1+.30*Math.sin(i*4.17));
    waves.push(new THREE.Vector4(Math.cos(angle),Math.sin(angle),k,amplitude));
    phases.push(new THREE.Vector2(Math.sqrt(9.81*k*Math.tanh(k*8)),i*2.399+Math.sin(i*9)*3));
  }
  return {waves,phases};
}

export class OceanRenderer {
  constructor(canvas) {
    this.canvas=canvas;
    this.renderer=new THREE.WebGLRenderer({canvas,antialias:true,alpha:false,powerPreference:'high-performance'});
    this.renderer.setPixelRatio(1);this.renderer.setClearColor(0x142b3a);this.renderer.autoClear=false;
    this.renderer.debug.onShaderError=(context,program,vertex,fragment)=>{throw new Error(context.getShaderInfoLog(vertex)+'\n'+context.getShaderInfoLog(fragment));};
    this.scene=new THREE.Scene();this.camera=new THREE.PerspectiveCamera(56,1,.1,6500);
    const spectrum=waveSpectrum();
    this.uniforms={uTime:{value:5.6},uWave:{value:1.2},uWind:{value:.45},uSun:{value:5},uProfile:{value:makeProfileTexture()},uWaves:{value:spectrum.waves},uPhases:{value:spectrum.phases},uFoam:{value:null}};
    this.lastTime=null;this.meshQuality='fine';
    this.setupSky();this.setupWater();this.setupBeach();this.setupFoam();this.setupSpray();
  }
  setupSky() {
    const material=new THREE.ShaderMaterial({uniforms:this.uniforms,depthWrite:false,depthTest:false,side:THREE.BackSide,
      vertexShader:'varying vec3 vRay;void main(){vec4 p=modelMatrix*vec4(position,1.);vRay=p.xyz-cameraPosition;gl_Position=projectionMatrix*viewMatrix*p;}',
      fragmentShader:environment+'varying vec3 vRay;void main(){gl_FragColor=vec4(tone(sky(normalize(vRay),true)),1.);}' });
    const mesh=new THREE.Mesh(new THREE.SphereGeometry(5200,24,12),material);mesh.renderOrder=-10;mesh.frustumCulled=false;this.scene.add(mesh);
  }
  setupWater() {
    this.seaGeometry=makeSeaGeometry();
    const material=new THREE.ShaderMaterial({uniforms:this.uniforms,side:THREE.DoubleSide,
      vertexShader:environment+surfaceModel+`
       varying vec3 vWorld,vNormal;varying vec2 vCA;varying vec4 vProfile;
       void main(){vec2 ca=position.xz;vec3 p=surfaceAt(ca);vec3 dc=surfaceAt(ca+vec2(.035,0.))-surfaceAt(ca-vec2(.035,0.));vec3 da=surfaceAt(ca+vec2(0.,.08))-surfaceAt(ca-vec2(0.,.08));vNormal=normalize(cross(dc,da));vWorld=p;vCA=ca;vProfile=profileAt(ca);gl_Position=projectionMatrix*viewMatrix*vec4(p,1.);}`,
      fragmentShader:environment+surfaceModel+`
       uniform sampler2D uFoam;
       varying vec3 vWorld,vNormal;varying vec2 vCA;varying vec4 vProfile;
       void main(){
        float coast=shore(vCA.y);float depth=(coast-vCA.x)*.18;
        vec3 view=normalize(cameraPosition-vWorld);float distance=length(cameraPosition-vWorld);
        vec3 n=normalize(vNormal);if(!gl_FrontFacing)n=-n;
        vec2 uv=vWorld.xz*.65+vec2(uTime*.035,-uTime*.05);
        float f=fbm(uv),dx=fbm(uv+vec2(.025,0.))-f,dz=fbm(uv+vec2(0.,.025))-f;
        float detail=(.035+uWind*.085)*exp(-distance*.018)*(1.-vProfile.a*.45);
        n=normalize(n+vec3(-dx,0.,-dz)*detail/.025);
        vec3 sd=sunDirection(),r=reflect(-view,n);float reflectedHorizon=smoothstep(-.12,.06,r.y);r.y=max(.002,r.y);
        float day=smoothstep(5.,22.,uSun),dusk=1.-smoothstep(-3.,3.,uSun);
        float fresnel=.0204+.9796*pow(1.-sat(dot(view,n)),5.);
        vec3 reflected=sky(r,false);
        vec3 deep=mix(vec3(.008,.042,.052),vec3(.012,.105,.145),day);
        vec3 shallow=mix(vec3(.014,.16,.145),vec3(.035,.35,.29),day);
        vec3 body=mix(shallow,deep,smoothstep(0.,5.,depth));
        float backlit=pow(sat(dot(view,sd)),3.);float thin=sat(vWorld.y/(uWave*.9));
        body+=vec3(.025,.22,.16)*thin*(.25+backlit*.75)*(1.-dusk*.45);
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
        foam=max(foam,vProfile.b*.42);
        float turbulence=fbm(vWorld.xz*2.7+vec2(-uTime*.25,uTime*.11));
        float tiny=noise(vWorld.xz*47.+vec2(uTime*.7,0.));
        foam=smoothstep(.09,.82,foam)*mix(.12,1.,smoothstep(.35,.67,turbulence+tiny*.07));
        vec3 white=mix(vec3(.74,.85,.82),vec3(.98,1.04,1.02),day);white=mix(white,vec3(.24,.33,.46),dusk);white*=(.68+.32*sat(dot(n,sd)))*(.65+tiny*.35);
        col=mix(col,white,foam);
        // Water under the curling lip is shaded; the exposed thin rim glows.
        float cavity=smoothstep(.38,.72,vProfile.a)*smoothstep(.25,.8,vProfile.g)*(1.-sat(n.y))*.20;
        col*=(1.-cavity)*mix(.52,1.,smoothstep(-.30,.10,vNormal.y));
        float fog=1.-exp(-distance*.0018);col=mix(col,sky(normalize(vec3(-view.x,.005,-view.z)),false),min(.94,fog));
        gl_FragColor=vec4(tone(col),1.);
       }`});
    this.water=new THREE.Mesh(this.seaGeometry,material);this.water.frustumCulled=false;this.scene.add(this.water);
  }
  setupBeach() {
    const geometry=this.seaGeometry;
    const material=new THREE.ShaderMaterial({uniforms:this.uniforms,side:THREE.DoubleSide,
      vertexShader:environment+surfaceModel+`varying vec3 vWorld;varying vec2 vCA;void main(){vec2 ca=position.xz;vec2 xz=worldXZ(ca);float h=min((ca.x-shore(ca.y))*.18,.95)+noise(ca*.7)*.015;vWorld=vec3(xz.x,h,xz.y);vCA=ca;gl_Position=projectionMatrix*viewMatrix*vec4(vWorld,1.);}`,
      fragmentShader:environment+surfaceModel+`varying vec3 vWorld;varying vec2 vCA;void main(){float d=vCA.x-shore(vCA.y);float day=smoothstep(5.,22.,uSun);float grain=noise(vCA*95.);vec3 col=mix(vec3(.25,.145,.085),vec3(.57,.42,.25),day)*(.93+grain*.10);float wet=1.-smoothstep(-.5,4.,d);vec3 view=normalize(cameraPosition-vWorld);vec3 n=normalize(vec3(-.169,1.,.0614));vec3 r=reflect(-view,n);col=mix(col,col*.35+sky(r,false)*.23,wet);col+=vec3(1.,.53,.16)*pow(sat(dot(r,sunDirection())),250.)*wet;float distance=length(vWorld-cameraPosition);col=mix(col,sky(normalize(vec3(-view.x,.005,-view.z)),false),min(.9,1.-exp(-distance*.0018)));gl_FragColor=vec4(tone(col),1.);}`});
    const beach=new THREE.Mesh(geometry,material);beach.frustumCulled=false;this.beach=beach;this.scene.add(beach);
  }
  setupFoam() {
    const options={type:THREE.UnsignedByteType,format:THREE.RGBAFormat,minFilter:THREE.LinearFilter,magFilter:THREE.LinearFilter,depthBuffer:false};
    this.foamA=new THREE.WebGLRenderTarget(768,768,options);this.foamB=this.foamA.clone();
    this.foamUniforms={...this.uniforms,uPrevious:{value:this.foamA.texture},uDt:{value:1/60}};
    this.foamScene=new THREE.Scene();this.foamCamera=new THREE.OrthographicCamera(-1,1,1,-1,0,1);
    const material=new THREE.ShaderMaterial({uniforms:this.foamUniforms,depthTest:false,depthWrite:false,
      vertexShader:'varying vec2 vUv;void main(){vUv=uv;gl_Position=vec4(position.xy,0.,1.);}',
      fragmentShader:environment+surfaceModel+`uniform sampler2D uPrevious;uniform float uDt;varying vec2 vUv;void main(){vec2 ca=vUv*vec2(60.,160.)+vec2(-35.,-45.);float d=shore(ca.y)-ca.x;vec2 velocity=vec2(1.0+1.8*(1.-smoothstep(0.,12.,d)),.15*sin(ca.x*.45+uTime*.3));vec2 previous=vUv-velocity*uDt/vec2(60.,160.);float old=texture2D(uPrevious,previous).r*exp(-uDt*.40);vec4 profile=profileAt(ca);float source=profile.b*(.5+noise(ca*2.2+uTime*.05)*.5)*smoothstep(-.5,.5,d);float foam=max(old,source*(1.-exp(-uDt*15.)));foam+=source*uDt*1.5;foam*=smoothstep(-1.3,-.1,d);gl_FragColor=vec4(min(1.,foam),0.,0.,1.);}`});
    this.foamScene.add(new THREE.Mesh(new THREE.PlaneGeometry(2,2),material));
    this.renderer.setRenderTarget(this.foamA);this.renderer.clearColor();this.renderer.setRenderTarget(this.foamB);this.renderer.clearColor();this.renderer.setRenderTarget(null);
    this.uniforms.uFoam.value=this.foamA.texture;
  }
  setupSpray() {
    const count=11000,values=new Float32Array(count*3);
    for(let i=0;i<count;i++){values[i*3]=(Math.sin(i*127.1)*43758.5453)%1;values[i*3]=Math.abs(values[i*3]);values[i*3+1]=Math.abs((Math.sin(i*311.7)*27182.818)%1);values[i*3+2]=Math.abs((Math.sin(i*74.7)*31415.92)%1);}
    const geo=new THREE.BufferGeometry();geo.setAttribute('position',new THREE.BufferAttribute(values,3));
    const material=new THREE.ShaderMaterial({uniforms:this.uniforms,transparent:true,depthWrite:false,blending:THREE.NormalBlending,
      vertexShader:environment+surfaceModel+`varying float vAlpha;void main(){float along=-35.+position.x*140.;float cross=shore(along)-5.4;float period=20./2.35;float phase=mod((uTime-(cross+phaseOffset(along))/2.35),period);float age=phase-position.y*.8;float alive=step(0.,age)*(1.-step(1.15,age));age=max(0.,age);vec2 ca=vec2(cross+1.8+age*(1.4+position.z*1.6),along+(position.z-.5)*age*1.4);vec2 xz=worldXZ(ca);float y=uWave*(.60+position.y*.15)+age*(.7+position.z*1.9)-4.9*age*age;vec3 p=vec3(xz.x,max(.02,y),xz.y);vec4 mv=viewMatrix*vec4(p,1.);gl_Position=projectionMatrix*mv;gl_PointSize=clamp((22.+position.z*24.)/max(1.,-mv.z),.6,3.5);vAlpha=alive*smoothstep(0.,.12,age)*(1.-smoothstep(.45,1.15,age))*.45*step(.03,y);}`,
      fragmentShader:environment+`varying float vAlpha;void main(){float d=length(gl_PointCoord-.5);if(d>.5||vAlpha<.01)discard;float day=smoothstep(5.,22.,uSun);vec3 c=mix(vec3(.95,.72,.44),vec3(.86,.98,1.),day);gl_FragColor=vec4(c,vAlpha*(1.-smoothstep(.2,.5,d)));}`});
    const spray=new THREE.Points(geo,material);spray.frustumCulled=false;this.scene.add(spray);
  }
  resize(width,height){this.renderer.setSize(width,height,false);this.camera.aspect=width/height;this.camera.updateProjectionMatrix();}
  draw(state) {
    const meshQuality=state.quality==='low'||state.scale<.55?'low':'fine';
    if(meshQuality!==this.meshQuality){
      const previous=this.seaGeometry;this.seaGeometry=meshQuality==='low'?makeSeaGeometry(320,240):makeSeaGeometry();
      this.water.geometry=this.beach.geometry=this.seaGeometry;previous.dispose();this.meshQuality=meshQuality;
    }
    this.uniforms.uTime.value=state.time;this.uniforms.uWave.value=state.wave;this.uniforms.uWind.value=state.wind;this.uniforms.uSun.value=state.sun;
    const mobile=1-smooth(.6,1.1,this.camera.aspect);
    const yaw=state.yaw+mobile*.10-.22;
    this.camera.position.set(2.6,3.0+state.distance,7.5);
    this.camera.lookAt(this.camera.position.x+Math.sin(yaw)*30,this.camera.position.y+Math.sin(-.115+state.pitch)*30,this.camera.position.z-Math.cos(yaw)*30);
    if(this.lastTime===null){
      for(let i=0;i<48;i++){
        this.uniforms.uTime.value=state.time-1.92+i*.04;this.foamUniforms.uDt.value=.04;this.foamUniforms.uPrevious.value=this.foamA.texture;
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
