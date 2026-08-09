(() => {
  "use strict";

  const TAU = Math.PI * 2;
  const PALETTES = {
    gold: { name:"电影暖金", hot:"#fff7d2", mid:"#ffc66f", cool:"#9c4cff", tint:[1.0,.82,.56], temperature:5600, exposure:1.02, bloom:1.55, chroma:.06 },
    blue: { name:"蓝白高温", hot:"#ffffff", mid:"#9aeaff", cool:"#315dff", tint:[.68,.94,1.16], temperature:9200, exposure:1.12, bloom:1.92, chroma:.22 },
    violet: { name:"紫色电浆", hot:"#fff5ff", mid:"#d49aff", cool:"#6537d8", tint:[.92,.68,1.14], temperature:7700, exposure:1.06, bloom:1.78, chroma:.78 },
    red: { name:"暗红巨兽", hot:"#fff0d4", mid:"#ff7658", cool:"#7f153e", tint:[1.12,.48,.32], temperature:4300, exposure:1.1, bloom:1.7, chroma:.46 }
  };

  function hexRgb(hex) {
    const value = Number.parseInt(hex.slice(1), 16);
    return [((value >> 16) & 255) / 255, ((value >> 8) & 255) / 255, (value & 255) / 255];
  }

  function rgba(hex, alpha) {
    const [r, g, b] = hexRgb(hex).map((value) => Math.round(value * 255));
    return `rgba(${r},${g},${b},${alpha})`;
  }

  const LUT_W = 384;
  const LUT_H = 288;
  const PHI_MAX = Math.PI * 4;
  const BETA_MAX = .78;
  const CAMERA_RADIUS = 18;
  const INITIAL_U = 1 / CAMERA_RADIUS;

  function integrateOrbitLut() {
    const orbit = new Float32Array(LUT_W * LUT_H);
    const phiEnd = new Float32Array(LUT_W);
    const dPhi = PHI_MAX / (LUT_H - 1), subSteps = 3, h = dPhi / subSteps;
    const deriv = (u) => 1.5 * u * u - u;
    for (let x = 0; x < LUT_W; x += 1) {
      const beta = ((x + .5) / LUT_W) * BETA_MAX;
      let u = INITIAL_U, v = beta < 1e-5 ? 1e6 : INITIAL_U / Math.tan(beta), active = true, end = -1;
      for (let y = 0; y < LUT_H; y += 1) {
        orbit[y * LUT_W + x] = active ? u : -1;
        if (!active) continue;
        for (let step = 0; step < subSteps; step += 1) {
          const k1u = v, k1v = deriv(u);
          const u2 = u + .5 * h * k1u, v2 = v + .5 * h * k1v, k2u = v2, k2v = deriv(u2);
          const u3 = u + .5 * h * k2u, v3 = v + .5 * h * k2v, k3u = v3, k3v = deriv(u3);
          const u4 = u + h * k3u, v4 = v + h * k3v, k4u = v4, k4v = deriv(u4);
          u += h * (k1u + 2 * k2u + 2 * k3u + k4u) / 6;
          v += h * (k1v + 2 * k2v + 2 * k3v + k4v) / 6;
          if (!Number.isFinite(u) || u >= 1) { active = false; end = -1; break; }
          if (v < 0 && u <= .00035) { active = false; end = (y + step / subSteps) * dPhi; break; }
        }
      }
      phiEnd[x] = end;
    }
    return { orbit, phiEnd };
  }

  const vertexSource = `#version 300 es
    layout(location=0) in vec2 aPosition;
    out vec2 vUv;
    void main(){vUv=aPosition*.5+.5;gl_Position=vec4(aPosition,0.,1.);}
  `;

  const fragmentSource = `#version 300 es
    precision highp float;
    uniform vec2 uResolution;
    uniform float uTime;
    uniform float uExposure;
    uniform float uYaw;
    uniform float uPitch;
    uniform float uRoll;
    uniform float uZoom;
    uniform float uTemperature;
    uniform float uThickness;
    uniform float uLensStrength;
    uniform float uChromatic;
    uniform float uHit;
    uniform vec3 uTint;
    uniform sampler2D uOrbitLut;
    uniform sampler2D uPhiEndLut;
    out vec4 outColor;
    #define PI 3.14159265359
    const float PHI_MAX=${PHI_MAX.toFixed(9)};
    const float BETA_MAX=${BETA_MAX.toFixed(6)};
    const float CAMERA_RADIUS=${CAMERA_RADIUS.toFixed(1)};

    float hash21(vec2 p){p=fract(p*vec2(123.34,456.21));p+=dot(p,p+45.32);return fract(p.x*p.y);}
    float hash31(vec3 p){p=fract(p*.1031);p+=dot(p,p.yzx+33.33);return fract((p.x+p.y)*p.z);}
    float noise3(vec3 p){
      vec3 i=floor(p),f=fract(p);f=f*f*(3.-2.*f);
      float n000=hash31(i),n100=hash31(i+vec3(1,0,0));
      float n010=hash31(i+vec3(0,1,0)),n110=hash31(i+vec3(1,1,0));
      float n001=hash31(i+vec3(0,0,1)),n101=hash31(i+vec3(1,0,1));
      float n011=hash31(i+vec3(0,1,1)),n111=hash31(i+vec3(1,1,1));
      return mix(mix(mix(n000,n100,f.x),mix(n010,n110,f.x),f.y),mix(mix(n001,n101,f.x),mix(n011,n111,f.x),f.y),f.z);
    }
    float fbm3(vec3 p){float v=0.,a=.54;for(int i=0;i<3;i++){v+=a*noise3(p);p=vec3(p.y+p.z,p.z-p.x,p.x+p.y)*1.31+17.17;a*=.48;}return v;}

    vec3 volumeCloud(vec3 hit,float t,float lensOrder){
      float r=length(hit.xz),az=atan(hit.z,hit.x),omega=1.28/pow(r,1.5),flowAz=az-t*omega;
      vec2 circle=vec2(cos(flowAz),sin(flowAz));
      float halfHeight=(.3+.105*r)*uThickness,yn=hit.y/max(halfHeight,.001);
      vec3 domain=vec3(circle*.88,r*.145+yn*.18)+vec3(0.,0.,t*.0042);
      vec3 distortion=vec3(noise3(domain*.72+vec3(3.7,-6.2,1.4)),noise3(domain*.69+vec3(-8.1,2.6,5.3)),noise3(domain*.75+vec3(4.4,9.1,-3.2)))-.5;
      vec3 shapeP=domain+distortion*1.42;
      float shape=fbm3(shapeP),coverage=smoothstep(.3,.68,shape),surfacePuff=noise3(shapeP*1.82+vec3(6.4,-2.7,8.1));
      float centreShift=distortion.y*.34,localTop=.86+.28*coverage;
      float profile=1.-smoothstep(localTop*.5,localTop,abs(yn-centreShift));
      float baseDensity=profile*(.22+.78*coverage);
      vec3 detailP=shapeP*3.55+vec3(yn*.55,-yn*.37,t*.008);
      float detail=fbm3(detailP),ridged=pow(clamp(1.-abs(detail*2.-1.),0.,1.),1.28);
      float erosion=(1.-ridged)*(.16+.34*(1.-baseDensity)),lowerDeck=exp(-2.9*(yn+.34)*(yn+.34));
      float density=max(.075*profile+.055*lowerDeck,baseDensity-erosion);
      density*=.58+.58*ridged;density*=.9+.16*surfacePuff;
      float orderSmooth=smoothstep(.9,2.55,lensOrder);
      density=mix(density,(.36+.38*shape)*profile,orderSmooth*.9);
      vec3 lightStep=normalize(vec3(-.38,.68,.34));
      float od=density;
      od+=.72*smoothstep(.3,.68,fbm3(shapeP+lightStep*.34))*profile;
      od+=.48*smoothstep(.3,.68,noise3(shapeP+lightStep*.72))*profile;
      od+=.28*smoothstep(.3,.68,noise3(shapeP+lightStep*1.18))*profile;
      float lightTransmittance=exp(-.38*od);
      float relief=clamp(ridged*.82+detail*.18,0.,1.);relief=mix(relief,.58,orderSmooth);
      return vec3(clamp(density,0.,1.18),relief,lightTransmittance);
    }

    float sampleOrbit(float beta,float phi){
      if(phi<0.||phi>PHI_MAX||beta<0.||beta>BETA_MAX)return -1.;
      return max(texture(uOrbitLut,vec2(clamp(beta/BETA_MAX,0.,1.),clamp(phi/PHI_MAX,0.,1.))).r,0.);
    }
    vec2 sampleLensExit(float beta){
      float x=clamp(beta/BETA_MAX,0.,1.)*${(LUT_W - 1).toFixed(1)};
      int x0=int(floor(x)),x1=min(x0+1,${LUT_W - 1});float f=fract(x);
      float a=texelFetch(uPhiEndLut,ivec2(x0,0),0).r,b=texelFetch(uPhiEndLut,ivec2(x1,0),0).r;
      float va=step(0.,a),vb=step(0.,b),escape=mix(va,vb,smoothstep(0.,1.,f));
      float phi=(va>.5&&vb>.5)?mix(a,b,f):(va>.5?a:b);return vec2(phi,escape);
    }
    float sampleEscape(float beta){return sampleLensExit(clamp(beta,0.,BETA_MAX)).y;}

    vec3 planckRgb(float temperature){
      vec3 nm=vec3(680.,550.,440.);vec3 x=1.4387769e7/(nm*max(temperature,900.));
      vec3 b=1.e16/(pow(nm,vec3(5.))*(exp(min(x,vec3(70.)))-1.));
      return b/max(max(max(b.r,b.g),b.b),1e-8);
    }
    vec3 discEmission(vec3 hit,vec3 cameraPos,float lensOrder,vec3 cloudData){
      float r=length(hit.xz),edge=max(1.-sqrt(3./r),0.),tempShape=pow(3./r,.76)*pow(edge,.24);
      float baseTemp=(1750.+4300.*clamp(tempShape*2.5,0.,1.))*(uTemperature/5600.);
      float cloud=cloudData.x,billows=cloudData.y,volumeLight=cloudData.z;
      float betaOrb=sqrt(clamp(.5/(r-1.),0.,.82)),gamma=1./sqrt(1.-betaOrb*betaOrb);
      vec3 tangent=normalize(vec3(-hit.z,0.,hit.x));float lineVelocity=dot(tangent,normalize(cameraPos-hit));
      float grav=sqrt(max(1.-1./r,.001)),shift=clamp(grav/(gamma*(1.-betaOrb*lineVelocity)),.62,1.38);
      vec3 toViewer=normalize(cameraPos-hit),lightDirection=normalize(vec3(-hit.x*.18,.92,-hit.z*.18));
      float phaseCos=dot(toViewer,lightDirection),g=.48,hg=(1.-g*g)/pow(max(1.+g*g-2.*g*phaseCos,.02),1.5);
      float forwardScatter=clamp(hg*.32,.16,2.15);
      vec3 hot=planckRgb(baseTemp*mix(1.,shift,mix(.12,.72,uChromatic)))*vec3(1.18,.86,.56);
      vec3 dust=mix(vec3(.32,.11,.045),vec3(.9,.4,.14),smoothstep(.08,.9,cloud));
      vec3 spectral=mix(dust,hot,smoothstep(.18,1.02,cloud));
      float radialHeat=1.-smoothstep(3.2,8.15,r),heat=clamp((.1+.92*radialHeat)*(uTemperature/7200.)*mix(1.,shift,.52),0.,1.);
      vec3 thermalBands=mix(vec3(.13,.018,.42),vec3(.72,.12,1.08),smoothstep(.16,.62,heat));
      thermalBands=mix(thermalBands,vec3(1.12,.84,1.22),smoothstep(.58,.92,heat));
      float blueShift=smoothstep(-.56,.56,lineVelocity);vec3 dopplerBands=mix(vec3(1.12,.035,.19),vec3(.08,.32,1.18),blueShift);
      thermalBands=mix(thermalBands,dopplerBands,(1.-smoothstep(.68,.96,heat))*.38+.08);
      vec3 ionLines=mix(vec3(.94,.08,.46),vec3(.2,.52,1.12),smoothstep(.42,.9,heat));
      vec3 plasmaColour=mix(thermalBands,ionLines,smoothstep(.58,.92,billows)*.18);
      spectral=mix(spectral,plasmaColour,clamp(uChromatic*(.58+.22*billows),0.,.84));
      float beaming=clamp(mix(1.,pow(shift,1.35),.28),.72,1.34),radialFade=(1.-smoothstep(7.62,8.55,r))*smoothstep(3.02,3.38,r);
      float silverLining=clamp(fwidth(cloud)*8.,0.,.56),reliefMask=smoothstep(.1,.92,billows);
      float internalLight=.66+.18*volumeLight+.12*forwardScatter+.18*silverLining,cloudRelief=mix(.86,1.18,reliefMask);
      spectral*=mix(.92,1.08,reliefMask);
      float luminance=(.16+.86*cloud+.58*pow(clamp(cloud,0.,1.25),1.85))*(.46+.76*tempShape)*internalLight*cloudRelief;
      return spectral*uTint*luminance*beaming*radialFade*uExposure;
    }

    void main(){
      vec2 p=(gl_FragCoord.xy-.5*uResolution)/uResolution.y;
      float rollC=cos(uRoll),rollS=sin(uRoll);p=mat2(rollC,-rollS,rollS,rollC)*p;
      float pitchC=cos(uPitch);vec3 cameraPos=CAMERA_RADIUS*vec3(sin(uYaw)*pitchC,sin(uPitch),-cos(uYaw)*pitchC);
      vec3 radial=normalize(cameraPos),forward=-radial,right=normalize(cross(forward,vec3(0,1,0))),up=normalize(cross(right,forward));
      vec3 ray=normalize(forward+right*p.x*.82/uZoom+up*p.y*.82/uZoom);
      float cosBeta=clamp(dot(ray,-radial),-1.,1.),beta=acos(cosBeta),sinBeta=sqrt(max(1.-cosBeta*cosBeta,0.)),lensBeta=beta/max(uLensStrength,.2);
      vec3 e2=sinBeta>.00001?normalize(ray+cosBeta*radial):right;
      float basePhi=atan(-radial.y,e2.y);
      vec3 volumeCol=vec3(0.);float transmittance=1.;
      vec3 foregroundCol=vec3(0.);float foregroundTransmittance=1.;

      for(int q=0;q<10;q++){
        if(foregroundTransmittance>.012){
          float travel=mix(5.2,14.75,(float(q)+.5)/10.);vec3 directHit=cameraPos+ray*travel;float directR=length(directHit.xz);
          float directHalfHeight=(.12+.05*directR)*uThickness,directRadial=smoothstep(2.92,3.28,directR)*(1.-smoothstep(7.88,8.62,directR));
          float directHeightN=directHit.y/max(directHalfHeight,.001);
          float directCore=exp(-7.4*abs(directHeightN)),directDeck=exp(-4.2*(directHeightN+.2)*(directHeightN+.2));
          float directBody=exp(-2.35*directHeightN*directHeightN),directHalo=exp(-1.12*directHeightN*directHeightN);
          float directDensity=directRadial*(.07*directCore+.12*directDeck+.69*directBody+.12*directHalo);
          if(directDensity>.001){vec3 directCloud=volumeCloud(directHit,uTime,0.);directDensity*=clamp(directCloud.x*.94,0.,1.05);vec3 directEmission=discEmission(directHit,cameraPos,0.,directCloud);float directAlpha=1.-exp(-directDensity*.18);foregroundCol+=foregroundTransmittance*directEmission*directAlpha*1.12;foregroundTransmittance*=1.-directAlpha;}
        }
      }
      for(int k=0;k<3;k++){
        for(int s=0;s<13;s++){
          float slice=(float(s)-6.)*.051,phi=basePhi+float(k)*PI+slice;
          if(transmittance>.012){
            float invR=sampleOrbit(lensBeta,phi);
            if(invR>0.&&invR<1.){
              float pathOrder=max(phi/PI,0.),rr=1./invR;vec3 candidate=rr*(cos(phi)*radial+sin(phi)*e2);float discR=length(candidate.xz);
              float halfHeight=(.3+.105*discR)*uThickness,radialDensity=smoothstep(2.92,3.28,discR)*(1.-smoothstep(7.88,8.62,discR));
              float heightN=candidate.y/max(halfHeight,.001),razorCore=exp(-6.2*abs(heightN)),lowerDeck=exp(-2.8*(heightN+.32)*(heightN+.32));
              float emissiveBody=exp(-1.18*heightN*heightN),scatteringHalo=exp(-.48*heightN*heightN);
              float density=radialDensity*(.06*razorCore+.2*lowerDeck+.62*emissiveBody+.2*scatteringHalo);
              if(density>.001){vec3 cloudData=volumeCloud(candidate,uTime,pathOrder);density*=clamp(cloudData.x*.94,0.,1.05);vec3 emission=discEmission(candidate,cameraPos,pathOrder,cloudData);float orderAtten=exp(-.38*max(pathOrder-1.,0.)),orbitEndFade=1.-smoothstep(PHI_MAX-.52,PHI_MAX-.06,phi),alpha=(1.-exp(-density*.17))*orderAtten*orbitEndFade;volumeCol+=transmittance*emission*alpha*1.16;transmittance*=1.-alpha;}
            }
          }
        }
      }

      float opticalObjectY=p.y/max(uZoom*uLensStrength,.001),verticalLighting=mix(.74,1.18,smoothstep(-.24,.16,opticalObjectY));
      vec3 backgroundCol=volumeCol*verticalLighting;foregroundCol*=verticalLighting;
      float edgeWidth=max(fwidth(lensBeta)*1.15,BETA_MAX/${(LUT_W - 1).toFixed(1)}*1.25);
      float escapeState=lensBeta>=BETA_MAX?1.:sampleEscape(lensBeta),eventHorizonMask=smoothstep(.025,.975,escapeState);
      backgroundCol*=eventHorizonMask;
      float photonRim=lensBeta>=BETA_MAX?0.:pow(abs(sampleEscape(lensBeta+edgeWidth)-sampleEscape(lensBeta-edgeWidth)),1.8);
      vec3 rimTint=mix(vec3(1.18,.66,.27),vec3(.48,.78,1.32),uChromatic*.72);
      backgroundCol+=rimTint*photonRim*(.024+.045*uExposure);
      vec3 col=foregroundCol+foregroundTransmittance*backgroundCol;
      float vignette=1.-smoothstep(.53,.94,length(p*vec2(.72,1.)));col*=.45+.55*vignette;
      col+=uHit*mix(uTint,vec3(1.),.65)*(photonRim*.34+(1.-foregroundTransmittance)*.18);
      float sceneLuma=max(max(col.r,col.g),col.b);
      float sceneAlpha=max(1.-eventHorizonMask,smoothstep(.003,.05,sceneLuma));
      outColor=vec4(max(col,vec3(0.)),clamp(sceneAlpha,0.,1.));
    }
  `;

  const blurSource = `#version 300 es
    precision highp float;in vec2 vUv;out vec4 outColor;
    uniform sampler2D uImage;uniform vec2 uTexel;uniform vec2 uDirection;uniform float uThreshold;uniform float uRadiusScale;
    vec3 bright(vec2 uv){vec3 c=texture(uImage,uv).rgb;float l=max(max(c.r,c.g),c.b);return c*smoothstep(uThreshold,uThreshold+.24,l);}
    void main(){vec2 o=uTexel*uDirection*uRadiusScale;vec3 c=bright(vUv)*.227027;c+=bright(vUv+o*2.35)*.316216;c+=bright(vUv-o*2.35)*.316216;c+=bright(vUv+o*5.85)*.070270;c+=bright(vUv-o*5.85)*.070270;outColor=vec4(c,0.);}
  `;

  const compositeSource = `#version 300 es
    precision highp float;in vec2 vUv;out vec4 outColor;
    uniform sampler2D uScene;uniform sampler2D uBloom;uniform float uBloomGain;
    void main(){vec4 scene=texture(uScene,vUv);vec3 bloom=texture(uBloom,vUv).rgb;vec3 c=scene.rgb+bloom*uBloomGain;c*=vec3(1.02,1.,.97);c=1.-exp(-c*1.42);c=pow(max(c,vec3(0.)),vec3(.4545));vec2 edgeP=(vUv-.5)*2.;float edgeFade=1.-smoothstep(.72,1.,length(edgeP));float alpha=max(scene.a,smoothstep(.035,.14,max(max(c.r,c.g),c.b)))*edgeFade;outColor=vec4(c*edgeFade,alpha);}
  `;

  class SharedBlackHoleRenderer {
    constructor(size = 224) {
      this.canvas = document.createElement("canvas");
      this.canvas.width = this.canvas.height = size;
      this.gl = this.canvas.getContext("webgl2", {alpha:true,antialias:false,depth:false,stencil:false,premultipliedAlpha:false,powerPreference:"high-performance"});
      this.ready = false;this.lastKey = "";this.lastFrame = -1;
      if (!this.gl) return;
      try {
        const gl = this.gl, hdrFloat = !!gl.getExtension("EXT_color_buffer_float"), floatLinear = gl.getExtension("OES_texture_float_linear");
        const compile = (type, source) => {const shader=gl.createShader(type);gl.shaderSource(shader,source);gl.compileShader(shader);if(!gl.getShaderParameter(shader,gl.COMPILE_STATUS))throw new Error(gl.getShaderInfoLog(shader));return shader;};
        const makeProgram = (fragment) => {const program=gl.createProgram();gl.attachShader(program,compile(gl.VERTEX_SHADER,vertexSource));gl.attachShader(program,compile(gl.FRAGMENT_SHADER,fragment));gl.linkProgram(program);if(!gl.getProgramParameter(program,gl.LINK_STATUS))throw new Error(gl.getProgramInfoLog(program));return program;};
        this.sceneProgram=makeProgram(fragmentSource);this.blurProgram=makeProgram(blurSource);this.compositeProgram=makeProgram(compositeSource);
        const buffer=gl.createBuffer();gl.bindBuffer(gl.ARRAY_BUFFER,buffer);gl.bufferData(gl.ARRAY_BUFFER,new Float32Array([-1,-1,1,-1,-1,1,-1,1,1,-1,1,1]),gl.STATIC_DRAW);gl.enableVertexAttribArray(0);gl.vertexAttribPointer(0,2,gl.FLOAT,false,0,0);
        const lookup=integrateOrbitLut();
        const floatTexture=(width,height,data,useLinear=true)=>{const texture=gl.createTexture();gl.bindTexture(gl.TEXTURE_2D,texture);gl.pixelStorei(gl.UNPACK_ALIGNMENT,1);const filter=useLinear&&floatLinear?gl.LINEAR:gl.NEAREST;gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MIN_FILTER,filter);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MAG_FILTER,filter);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_WRAP_S,gl.CLAMP_TO_EDGE);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_WRAP_T,gl.CLAMP_TO_EDGE);gl.texImage2D(gl.TEXTURE_2D,0,gl.R32F,width,height,0,gl.RED,gl.FLOAT,data);return texture;};
        this.orbitTexture=floatTexture(LUT_W,LUT_H,lookup.orbit,true);this.phiTexture=floatTexture(LUT_W,1,lookup.phiEnd,false);
        const colorTarget=(width,height)=>{const texture=gl.createTexture();gl.bindTexture(gl.TEXTURE_2D,texture);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MIN_FILTER,gl.LINEAR);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MAG_FILTER,gl.LINEAR);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_WRAP_S,gl.CLAMP_TO_EDGE);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_WRAP_T,gl.CLAMP_TO_EDGE);gl.texImage2D(gl.TEXTURE_2D,0,hdrFloat?gl.RGBA16F:gl.RGBA8,width,height,0,gl.RGBA,hdrFloat?gl.HALF_FLOAT:gl.UNSIGNED_BYTE,null);const fbo=gl.createFramebuffer();gl.bindFramebuffer(gl.FRAMEBUFFER,fbo);gl.framebufferTexture2D(gl.FRAMEBUFFER,gl.COLOR_ATTACHMENT0,gl.TEXTURE_2D,texture,0);return {texture,fbo,width,height};};
        this.sceneTarget=colorTarget(size,size);this.blurA=colorTarget(Math.floor(size/4),Math.floor(size/4));this.blurB=colorTarget(Math.floor(size/4),Math.floor(size/4));
        this.uniforms=Object.fromEntries(["uResolution","uTime","uExposure","uYaw","uPitch","uRoll","uZoom","uTemperature","uThickness","uLensStrength","uChromatic","uHit","uTint"].map((name)=>[name,gl.getUniformLocation(this.sceneProgram,name)]));
        gl.useProgram(this.sceneProgram);gl.activeTexture(gl.TEXTURE0);gl.bindTexture(gl.TEXTURE_2D,this.orbitTexture);gl.uniform1i(gl.getUniformLocation(this.sceneProgram,"uOrbitLut"),0);gl.activeTexture(gl.TEXTURE1);gl.bindTexture(gl.TEXTURE_2D,this.phiTexture);gl.uniform1i(gl.getUniformLocation(this.sceneProgram,"uPhiEndLut"),1);
        this.ready=true;
      } catch (error) {console.warn("Black-hole material fallback enabled",error);}
    }

    bindTexture(program,name,unit,texture){const gl=this.gl;gl.useProgram(program);gl.activeTexture(gl.TEXTURE0+unit);gl.bindTexture(gl.TEXTURE_2D,texture);gl.uniform1i(gl.getUniformLocation(program,name),unit);}

    render(enemy, elapsed) {
      if (!this.ready) return false;
      const frame=Math.floor(elapsed*this.targetFps),palette=PALETTES[enemy.blackHolePalette]||PALETTES.violet,key=`${enemy.id}:${enemy.blackHolePalette}:${frame}:${enemy.hit>0?1:0}`;
      if(key===this.lastKey)return true;this.lastKey=key;
      const gl=this.gl,scene=this.sceneTarget;
      gl.bindFramebuffer(gl.FRAMEBUFFER,scene.fbo);gl.viewport(0,0,scene.width,scene.height);gl.clearColor(0,0,0,0);gl.clear(gl.COLOR_BUFFER_BIT);gl.useProgram(this.sceneProgram);
      gl.activeTexture(gl.TEXTURE0);gl.bindTexture(gl.TEXTURE_2D,this.orbitTexture);gl.activeTexture(gl.TEXTURE1);gl.bindTexture(gl.TEXTURE_2D,this.phiTexture);
      gl.uniform2f(this.uniforms.uResolution,scene.width,scene.height);gl.uniform1f(this.uniforms.uTime,elapsed+(enemy.visualSeed||enemy.phase||0));gl.uniform1f(this.uniforms.uExposure,palette.exposure);gl.uniform1f(this.uniforms.uYaw,(enemy.visualYaw||0)*Math.PI/180);gl.uniform1f(this.uniforms.uPitch,(enemy.visualPitch||14)*Math.PI/180);gl.uniform1f(this.uniforms.uRoll,(enemy.visualRoll||0)*Math.PI/180);gl.uniform1f(this.uniforms.uZoom,.84);gl.uniform1f(this.uniforms.uTemperature,palette.temperature);gl.uniform1f(this.uniforms.uThickness,1.42);gl.uniform1f(this.uniforms.uLensStrength,1.28);gl.uniform1f(this.uniforms.uChromatic,palette.chroma);gl.uniform1f(this.uniforms.uHit,enemy.hit>0?Math.min(1,enemy.hit*7):0);gl.uniform3fv(this.uniforms.uTint,palette.tint);gl.drawArrays(gl.TRIANGLES,0,6);
      const blurA=this.blurA,blurB=this.blurB,opticalScale=1.05;
      gl.bindFramebuffer(gl.FRAMEBUFFER,blurA.fbo);gl.viewport(0,0,blurA.width,blurA.height);this.bindTexture(this.blurProgram,"uImage",2,scene.texture);gl.uniform2f(gl.getUniformLocation(this.blurProgram,"uTexel"),1/scene.width,1/scene.height);gl.uniform2f(gl.getUniformLocation(this.blurProgram,"uDirection"),1,0);gl.uniform1f(gl.getUniformLocation(this.blurProgram,"uThreshold"),.4);gl.uniform1f(gl.getUniformLocation(this.blurProgram,"uRadiusScale"),opticalScale);gl.drawArrays(gl.TRIANGLES,0,6);
      gl.bindFramebuffer(gl.FRAMEBUFFER,blurB.fbo);gl.viewport(0,0,blurB.width,blurB.height);this.bindTexture(this.blurProgram,"uImage",2,blurA.texture);gl.uniform2f(gl.getUniformLocation(this.blurProgram,"uTexel"),1/blurA.width,1/blurA.height);gl.uniform2f(gl.getUniformLocation(this.blurProgram,"uDirection"),0,1);gl.uniform1f(gl.getUniformLocation(this.blurProgram,"uThreshold"),-1);gl.uniform1f(gl.getUniformLocation(this.blurProgram,"uRadiusScale"),opticalScale);gl.drawArrays(gl.TRIANGLES,0,6);
      gl.bindFramebuffer(gl.FRAMEBUFFER,null);gl.viewport(0,0,this.canvas.width,this.canvas.height);gl.clearColor(0,0,0,0);gl.clear(gl.COLOR_BUFFER_BIT);this.bindTexture(this.compositeProgram,"uScene",2,scene.texture);this.bindTexture(this.compositeProgram,"uBloom",3,blurB.texture);gl.uniform1f(gl.getUniformLocation(this.compositeProgram,"uBloomGain"),palette.bloom);gl.drawArrays(gl.TRIANGLES,0,6);
      return true;
    }
  }

  const MAX_GAME_BOSS_DIAMETER = 360;
  const RENDER_FRAME_PADDING = 1.08;
  const lowPowerDevice = (navigator.hardwareConcurrency || 8) <= 4;
  const rendererDpr = Math.min(lowPowerDevice ? 1 : 1.15, window.devicePixelRatio || 1);
  const rendererSize = Math.max(lowPowerDevice ? 352 : 384, Math.min(lowPowerDevice ? 384 : 448, Math.ceil(MAX_GAME_BOSS_DIAMETER * RENDER_FRAME_PADDING * rendererDpr / 16) * 16));
  // Every visible frame is generated by the WebGL material. No bitmap boss
  // sprite is loaded; the higher internal resolution prevents magnified pixels.
  const renderer = new SharedBlackHoleRenderer(rendererSize);
  renderer.targetFps = lowPowerDevice ? 8 : 10;

  function visualExtent(radius) {
    const visibleDiameter = Math.min(MAX_GAME_BOSS_DIAMETER, radius * 5.44);
    return visibleDiameter * RENDER_FRAME_PADDING * .5;
  }

  function draw(ctx, enemy, radius, elapsed) {
    if (!renderer.render(enemy, elapsed)) return false;
    const extent = visualExtent(radius);
    ctx.save();ctx.globalAlpha=1;ctx.drawImage(renderer.canvas,-extent,-extent,extent*2,extent*2);ctx.restore();
    return true;
  }

  function spawnExplosion(particles, enemy, radius) {
    particles.push({type:"blackHoleDissolve",x:enemy.x,y:enemy.y,radius,blackHolePalette:enemy.blackHolePalette||"violet",visualYaw:enemy.visualYaw||0,visualRoll:enemy.visualRoll||0,visualPitch:enemy.visualPitch||14,seed:enemy.visualSeed||enemy.phase||1,life:1.9,maxLife:1.9});
  }

  function drawExplosion(ctx, particle) {
    const palette=PALETTES[particle.blackHolePalette]||PALETTES.violet,progress=1-particle.life/particle.maxLife,radius=particle.radius;
    const ease=1-Math.pow(1-progress,3),fade=Math.pow(1-progress,2.25),extent=visualExtent(radius);
    ctx.save();ctx.translate(particle.x,particle.y);ctx.rotate((particle.visualRoll||0)*Math.PI/180);

    // The event horizon loses opacity first, then its cloud body expands into
    // several coherent, softly blurred vapour layers. No rectangular fragments.
    ctx.globalCompositeOperation="source-over";ctx.globalAlpha=fade;ctx.filter=`blur(${(progress*5.5).toFixed(2)}px)`;ctx.drawImage(renderer.canvas,-extent*(1+ease*.035),-extent*(1+ease*.035)-ease*radius*.08,extent*2*(1+ease*.035),extent*2*(1+ease*.035));
    ctx.globalCompositeOperation="lighter";
    for(let i=0;i<7;i+=1){
      const phase=particle.seed*.19+i*2.17,side=i%2===0?1:-1,spread=ease*radius*(.18+i*.095),lift=ease*radius*(.12+.065*i);
      const scale=1+ease*(.04+i*.018);ctx.save();ctx.translate(side*spread+Math.sin(phase+progress*3)*radius*.08,-lift+Math.cos(phase)*radius*.06);ctx.scale(scale,scale);ctx.globalAlpha=fade*(.055+.018*(7-i));ctx.filter=`blur(${(3+progress*13+i*.65).toFixed(2)}px)`;ctx.drawImage(renderer.canvas,-extent,-extent,extent*2,extent*2);ctx.restore();
    }
    ctx.filter="none";

    // Soft coherent wisps replace sparks and radial blast rays.
    ctx.lineCap="round";
    for(let i=0;i<30;i+=1){
      const phase=particle.seed*.31+i*2.399,side=i%2===0?1:-1,spread=radius*(.45+((i*13)%17)/17*1.65)*ease;
      const x=side*spread+Math.sin(phase+progress*4)*radius*.2,y=(i/29-.5)*radius*1.65-progress*radius*(.25+.5*((i*7)%9)/9);
      const w=radius*(.18+.42*((i*11)%13)/13)*(1+.65*ease),h=radius*(.025+.055*((i*5)%7)/7);
      ctx.globalAlpha=fade*(.08+.2*((i*17)%19)/19);ctx.strokeStyle=i%3===0?palette.hot:i%3===1?palette.mid:palette.cool;ctx.shadowColor=ctx.strokeStyle;ctx.shadowBlur=radius*.12;ctx.lineWidth=Math.max(1.2,h*.55);ctx.beginPath();ctx.ellipse(x,y,w,h,Math.sin(phase)*.22,Math.PI*.08,Math.PI*.92);ctx.stroke();
    }

    const afterglow=ctx.createRadialGradient(0,0,0,0,0,radius*(.9+ease*1.5));afterglow.addColorStop(0,rgba(palette.hot,.18*fade));afterglow.addColorStop(.42,rgba(palette.mid,.13*fade));afterglow.addColorStop(1,rgba(palette.cool,0));ctx.globalAlpha=1;ctx.fillStyle=afterglow;ctx.beginPath();ctx.arc(0,0,radius*(.9+ease*1.5),0,TAU);ctx.fill();ctx.restore();
  }

  window.EndlessBlackHoleEnemy = { PALETTES, draw, spawnExplosion, drawExplosion };
})();
