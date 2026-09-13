/* Mineral grains, a shared perspective camera and a procedural slate stage.
 * No image textures: particles keep their seed and identity across every scene.
 * CPU offset helpers mirror shader trajectories for authoring and continuity checks.
 */
(() => {
  'use strict';
  const gemFraction = .003; // Default 1.5% total; five fixed species bands.
  function mineralKind(seed, enabled, share=gemFraction*5) {
    const band=seed*5,kind=Math.floor(band)+1;
    if(band-Math.floor(band)<share&&enabled[kind])return kind;
    return enabled[0]?0:-1;
  }
  const cameraMath = `
    vec3 rotateX(vec3 p, float a) {
      float c=cos(a),s=sin(a);return vec3(p.x,c*p.y-s*p.z,s*p.y+c*p.z);
    }
    vec3 rotateY(vec3 p, float a) {
      float c=cos(a),s=sin(a);return vec3(c*p.x+s*p.z,p.y,-s*p.x+c*p.z);
    }
    vec3 rotateZ(vec3 p, float a) {
      float c=cos(a),s=sin(a);return vec3(c*p.x-s*p.y,s*p.x+c*p.y,p.z);
    }
    vec3 cameraAngles() {
      return viewAngles;
    }
    vec3 toCamera(vec3 p) {
      vec3 a=cameraAngles();return rotateZ(rotateX(rotateY(p,a.y),a.x),a.z);
    }
    vec3 fromCamera(vec3 p) {
      vec3 a=cameraAngles();return rotateY(rotateX(rotateZ(p,-a.z),-a.x),-a.y);
    }
    vec2 followLightCentre(){return vec2(.72*sin(time*.13),.40*cos(time*.11+.7));}
    float followLight(vec2 p){
      vec2 d=p-followLightCentre();float a=.32*sin(time*.07),c=cos(a),s=sin(a);
      d=vec2(c*d.x-s*d.y,s*d.x+c*d.y)*vec2(1.65,3.1);
      return spotlight*exp(-dot(d,d));
    }
    float cameraDistance() {return 3.9;}
    float cameraFit() {
      return min(.68,aspect*.84)*viewZoom;
    }
    float cameraCentre() {return mix(.05,.20,smoothstep(.8,1.3,aspect));}
  `;
  const vertex = `precision highp float;
    attribute vec3 start;
    attribute vec3 finish;
    attribute vec3 normalStart;
    attribute vec3 normalFinish;
    attribute vec4 grain;
    uniform float progress;
    uniform float aspect;
    uniform float dpr;
    uniform float time;
    uniform float spotlight;
    uniform float camera;
    uniform vec3 viewAngles;
    uniform vec3 viewTarget;
    uniform float viewZoom;
    uniform float objectSpin;
    uniform float galoisLossFrom;
    uniform float galoisLossTo;
    uniform vec2 galoisFit;
    uniform float radiation;
    uniform float radiationFineOnly;
    uniform float grainTypes[6];
    uniform float extrusionFrom;
    uniform float twoSided;
    uniform float extrusionTo;
    uniform float gemShare;
    uniform float outroFall;
    uniform float outroExit;
    uniform mediump float complexity;
    uniform mediump float depth;
    uniform float wander;
    varying mediump vec3 color;
    varying mediump float opacity;
    varying mediump vec4 material;
    varying mediump float kind;
    varying mediump vec3 crystalLight;
    ${cameraMath}
    ${window.CourseOpeningImpulse?.shader||'vec3 impulseOffset(vec3 p){return vec3(0.);}'}

    // Only tagged grains belonging to the near figure yield to the cadence.
    // Their separate engraving layer never consumes the landscape behind it.
    vec4 storyLoss(vec3 point,float loss,float seed){
      float amount=clamp(loss,0.,1.);
      if(amount<=0.)return vec4(point,1.);
      float scale=max(.00001,galoisFit.x);
      float mask=step(.026,point.z/scale);
      float age=smoothstep(.10*seed,.72+.28*seed,amount);
      float travel=mask*age*(.32+.68*age);
      vec2 drift=vec2(-.025-.045*seed,-.080-.120*seed)*travel*scale;
      return vec4(point.xy+drift,point.z,1.-.97*mask*age);
    }

    vec2 localWander(vec2 p) {
      float a = time * .33;
      vec2 eddy = vec2(
        sin(p.y * 15. + a) * cos(p.x * 9. - time * .17),
        -sin(p.x * 15. - time * .28) * cos(p.y * 9. + time * .21)
      );
      vec2 drift = vec2(
        sin(time * (.42 + .45 * grain.z) + grain.x * 6.28318530718) *
          cos(time * .17 + grain.y * 6.28318530718),
        cos(time * (.36 + .40 * grain.w) + grain.y * 6.28318530718) *
          sin(time * .19 + grain.x * 6.28318530718)
      );
      vec2 fine = vec2(
        sin(time * 1.31 + grain.z * 6.28318530718),
        cos(time * 1.13 + grain.w * 6.28318530718)
      );
      return .0176 * wander * (.30 * eddy + .50 * drift + .20 * fine);
    }

    // Emission density is twice its original value across the full slider range.
    // A fixed minority of grains is continuously emitted along its true surface
    // normal. Each seed travels in one straight line at constant speed, fades
    // out, and returns to its source only while completely invisible.
    float emissionSelection() {
      float selector=fract(grain.x*37.17+grain.z*17.71);
      float fine=(1.-step(.64,grain.z))*(1.-step(.16,grain.y));
      return step(selector,radiation*.40)*step(.0001,radiation)*mix(1.,fine,radiationFineOnly);
    }
    vec4 escapeGrain(vec3 normal, float chosen) {
      float phase=fract(time/(2.8+grain.z*1.6)+grain.y*.754877666+grain.w*.569840296);
      float age=clamp(phase/.94,0.,1.);
      float reach=.06+.19*radiation;
      float life=smoothstep(0.,.04,phase)*(1.-smoothstep(.08,.94,phase));
      return vec4(normal*reach*age*chosen,mix(1.,life,chosen));
    }

    float mineralKind(float seed) {
      // Toggling a species never redistributes its share to other gemstones.
      float band=seed*5.;
      for(int i=1;i<6;i++){
        if(floor(band)==float(i-1)&&fract(band)<gemShare&&grainTypes[i]>.5)return float(i);
      }
      return grainTypes[0]>.5?0.:-1.;
    }

    vec3 mineral(float k) {
      if(k<.5)return vec3(.83,.66,.39);
      if(k<1.5)return vec3(.88,.95,1.);
      if(k<2.5)return vec3(.16,.39,.96);
      if(k<3.5)return vec3(.92,.16,.27);
      if(k<4.5)return vec3(.12,.72,.43);
      return vec3(.65,.32,.90);
    }

    void main() {
      kind=mineralKind(fract(grain.x*17.17+grain.w*31.31));
      float t=progress;
      float e=t*t*t*(t*(t*6.-15.)+10.);
      vec4 storyFrom=storyLoss(start,galoisLossFrom,grain.x);
      vec4 storyTo=storyLoss(finish,galoisLossTo,grain.x);
      vec2 delta=storyTo.xy-storyFrom.xy;
      float storyOpacity=mix(storyFrom.w,storyTo.w,e);
      float arch=sin(3.14159265359*e);
      vec3 p=mix(storyFrom.xyz,storyTo.xyz,e);
      p.z=mix(storyFrom.z*mix(1.,depth,extrusionFrom),storyTo.z*mix(1.,depth,extrusionTo),e);
      p.xy+=vec2(-delta.y,delta.x)*arch*.28;
      float dist=length(delta);
      p.xy+=vec2(sin(grain.x*19.+e*6.283),cos(grain.y*23.-e*6.283))*
        arch*min(.022,dist*.16);
      vec3 fromNormal=mix(normalStart,vec3(0.,0.,1.),extrusionFrom*(1.-depth));
      vec3 toNormal=mix(normalFinish,vec3(0.,0.,1.),extrusionTo*(1.-depth));
      vec3 n=mix(fromNormal,toNormal,e);
      if(length(n)<.001)n=vec3(0.,0.,1.);
      n=normalize(n);
      float emitted=emissionSelection();
      vec4 escaped=escapeGrain(n,emitted);
      // The closing inscription sheds only fine grains under gravity. Most of
      // each letter stays in place; an invisible reset continuously renews the sand.
      float falling=outroFall*(1.-step(.64,grain.z))*(1.-step(.20,grain.y));
      float fallPhase=fract(time/3.6+grain.x*.754877666+grain.w*.569840296);
      float fallAge=fallPhase*3.6;
      p.y-=falling*(.045*fallAge+.18*fallAge*fallAge);
      float fallLife=smoothstep(0.,.025,fallPhase)*(1.-smoothstep(.55,1.,fallPhase));
      escaped.w*=mix(1.,fallLife,falling);
      if(outroExit>=0.){
        // Every particle, including the signature, is released on the final cue.
        float releaseAge=max(0.,outroExit-grain.w*.65);
        p.y-=.12*releaseAge+.45*releaseAge*releaseAge;
        escaped.w*=1.-smoothstep(2.4,3.2,releaseAge);
      }
      // Emitted grains have a fixed source: local wandering applies only to
      // grains that remain in the figure, never to the outward trajectories.
      p.xy+=localWander(p.xy)*(1.-emitted)*(1.-falling);
      p+=escaped.xyz;
      p+=impulseOffset(p);
      // Object-space self-spin is independent of camera movement. Rotate both
      // the emitted position and its surface normal so lighting and outward
      // emission remain attached to the same rope as the figure turns.
      p=rotateZ(p,objectSpin);
      n=rotateZ(n,objectSpin);
      vec3 q=toCamera(p-viewTarget);
      float w=1.-camera*q.z/cameraDistance();
      float fit=cameraFit();
      // With camera=0 this is exactly the original flat XY framing. Z still
      // records true surface depth, allowing the near side of the torus to occlude.
      gl_Position=vec4(q.x*fit/aspect,q.y*fit+cameraCentre()*w,-q.z*.20,w);

      float variedSize=.58+.86*grain.y;
      if(grain.z>.64)variedSize=1.20+.70*grain.y;
      if(grain.z>.94)variedSize=1.95+.80*grain.y;
      float size=mix(1.25+.14*grain.z,variedSize,complexity);
      if(kind>.5)size*=1.18;
      if(falling>.5)size=min(size,.90);
      if(radiationFineOnly>.5&&emitted>.5)size=min(size,.80);
      // Grains grow more gently than the camera magnification, preserving a
      // fine, loose sand texture in close-ups instead of oversized pebbles.
      gl_PointSize=size*mix(1.,1.10,depth)*dpr*pow(viewZoom,.84)*clamp(1./w,.68,1.65);

      vec3 lamp=normalize(mix(vec3(-.52,.64,.79),vec3(followLightCentre()-p.xy,1.25),spotlight*.65));
      float diffuse=max(0.,dot(n,lamp));
      diffuse=mix(diffuse,abs(dot(n,lamp)),twoSided);
      float macroLight=.32+.75*diffuse;
      float lampFalloff=.84+.16*clamp(1.-length(p.xy-vec2(-.35,.48))*.5,0.,1.);
      vec3 lightInView=toCamera(lamp);crystalLight=vec3(lightInView.x,-lightInView.y,lightInView.z);
      vec3 tint=mineral(kind)*(.73+.27*grain.w);
      float luminance=dot(tint,vec3(.2126,.7152,.0722));
      // Warm, varied ordinary sand remains the body of every figure.
      vec3 sand=mix(vec3(.46,.33,.16),vec3(.91,.77,.49),grain.w);
      sand=mix(sand,vec3(.99,.91,.74),pow(grain.y,18.)*.55);
      color=(kind<.5?sand:mix(vec3(luminance),tint,.79))*macroLight*lampFalloff;
      vec3 eye=fromCamera(vec3(0.,0.,1.));
      float sheen=pow(max(0.,dot(n,normalize(lamp+eye))),24.);
      color+=vec3(.94,.78,.48)*sheen*.13;
      float beam=followLight(p.xy);
      color=color*(1.+beam*.62)+vec3(.12,.10,.065)*beam*(.3+.7*diffuse);
      opacity=(.65+.30*grain.x)*(1.-complexity*step(.94,grain.z)*.10)*escaped.w*storyOpacity;
      material=grain;
    }`;

  const fragment = `precision mediump float;
    uniform mediump float narrativeLight;
    uniform mediump float depth;
    uniform mediump float complexity;
    varying mediump vec3 color;
    varying mediump float opacity;
    varying mediump vec4 material;
    varying mediump float kind;
    varying mediump vec3 crystalLight;
    void main() {
      if(kind<-.5)discard;
      vec2 p=gl_PointCoord*2.-1.;
      float angle=material.x*6.28318530718;
      float c=cos(angle),s=sin(angle);
      vec2 turned=vec2(c*p.x+s*p.y,-s*p.x+c*p.y);
      float axis=.72+.28*material.y;
      vec2 shaped=vec2(turned.x/axis,turned.y);
      float polar=atan(shaped.y,shaped.x+.00001);
      float outline=.90+.055*sin(polar*5.+material.x*6.28318530718)+.035*sin(polar*3.+material.y*10.);
      float character=max(depth,complexity*.7);
      vec2 q=mix(p*vec2(1.,.84+material.z*.22),shaped/outline,character);
      float r=length(q);
      if(kind>.5){
        // A planar table and eight flat crown facets: no spherical/plastic lobe.
        vec2 cut=turned; if(kind>3.5&&kind<4.5)cut.x/=.73;
        vec2 edge=abs(cut);
        float cutRadius=kind<1.5?(edge.x+edge.y)*.86:max(max(edge.x,edge.y),(edge.x+edge.y)*.72);
        if(cutRadius>1.)discard;
        float sector=floor((atan(cut.y,cut.x)+3.14159265)/.78539816);
        float faceAngle=(sector+.5)*.78539816-3.14159265;
        float table=1.-step(.37,cutRadius);
        float tilt=mix(.84,.035,table);
        vec3 face=normalize(vec3(tilt*cos(faceAngle),tilt*sin(faceAngle),.72));
        face.xy=vec2(c*face.x-s*face.y,s*face.x+c*face.y);
        vec3 light=normalize(crystalLight),eye=vec3(0.,0.,1.);
        float incidence=max(0.,dot(face,light));
        float f0=kind<1.5?.17:.075;
        float fresnel=f0+(1.-f0)*pow(1.-max(0.,face.z),5.);
        float spec=pow(max(0.,dot(face,normalize(light+eye))),180.);
        vec3 reflection=reflect(-eye,face);
        // Sparse broad reflections of a studio window, separated by deep facets.
        float windowLight=pow(max(0.,dot(reflection,normalize(vec3(-.7,-.65,-.1)))),24.);
        float pavilion=floor((atan(cut.y,cut.x)+3.14159265)/.39269908);
        float internal=.5+.5*cos(mix(sector,pavilion,table)*2.39+material.w*6.28);
        vec3 transmitted=color*(.22+.55*incidence)*(.40+.60*internal);
        vec3 crystal=transmitted+vec3(.91,.96,1.)*(windowLight*(.22+fresnel*3.2)+spec*.85);
        // Colourless diamond reflects white light; coloured stones retain dark interiors.
        if(kind<1.5)crystal=mix(crystal,vec3(.68,.76,.82)*(.12+.27*internal),.24);
        float bevel=(1.-smoothstep(.018,.045,abs(cutRadius-.37)))*.05;
        crystal+=vec3(.73,.83,.91)*bevel;
        float alpha=(1.-smoothstep(.91,1.,cutRadius))*opacity;
        if(alpha<.075)discard;
        gl_FragColor=vec4(crystal*clamp(narrativeLight,.65,1.15),alpha);return;
      }
      if(r>1.)discard;
      float flatAlpha=1.-smoothstep(.25,1.,r);
      float flatShade=.74+.26*clamp(.5-p.x*.5+p.y*.2,0.,1.);
      vec3 flatColor=color*flatShade;
      vec2 nxy=vec2(q.x/axis,q.y);
      nxy+=.075*vec2(sin(q.y*6.+material.x*6.),cos(q.x*7.+material.y*6.))*r;
      nxy=vec2(c*nxy.x-s*nxy.y,s*nxy.x+c*nxy.y);
      vec3 n=normalize(vec3(nxy,sqrt(max(.008,1.-r*r))));
      vec3 lamp=normalize(vec3(-.52,-.64,.68));
      vec3 halfway=normalize(lamp+vec3(0.,0.,1.));
      float diffuse=max(0.,dot(n,lamp));
      float specular=pow(max(0.,dot(n,halfway)),20.+28.*material.z);
      float rim=1.-.30*smoothstep(.64,1.,r);
      vec3 solidColor=color*(.25+.91*diffuse)*rim;
      solidColor+=vec3(1.,.94,.79)*specular*(.20+.18*material.y);
      float solidAlpha=1.-smoothstep(.82,1.,r);
      float alpha=mix(flatAlpha,solidAlpha,depth)*opacity;
      // Transparent sprite corners must never occlude another side of the ring.
      if(alpha<.075)discard;
      gl_FragColor=vec4(mix(flatColor,solidColor,depth)*clamp(narrativeLight,.65,1.15),alpha);
    }`;

  const backgroundVertex = `attribute vec2 pos;varying vec2 uv;
    void main(){uv=pos;gl_Position=vec4(pos,1.,1.);}`;
  const backgroundFragment = `precision highp float;
    varying vec2 uv;
    uniform float aspect;
    uniform float time;
    uniform float spotlight;
    uniform float camera;
    uniform vec3 viewAngles;
    uniform vec3 viewTarget;
    uniform float viewZoom;
    uniform float background;
    uniform float stageLight;
    ${cameraMath}
    float hash(vec2 p){return fract(sin(dot(p,vec2(127.1,311.7)))*43758.5453);}
    float noise(vec2 p){
      vec2 i=floor(p),f=fract(p);f=f*f*(3.-2.*f);
      return mix(mix(hash(i),hash(i+vec2(1.,0.)),f.x),mix(hash(i+vec2(0.,1.)),hash(i+vec2(1.,1.)),f.x),f.y);
    }
    float strata(vec2 p){return .55*noise(p*2.1)+.28*noise(p*5.8+7.1)+.17*noise(p*17.3);}
    void main(){
      float grain=hash(floor(gl_FragCoord.xy))*.009;
      float glow=exp(-length((uv-vec2(-.5,.45))*vec2(.7,1.)))*.015;
      float vignette=1.-smoothstep(.25,1.5,length(uv));
      vec3 quiet=vec3(.018,.017,.014)+vec3(.6,.49,.28)*(glow+grain)*vignette;
      // Screen-anchored slate: foreground orbit, spin, zoom and pointer rotation
      // can never rotate or translate the background image.
      vec2 p=vec2(uv.x*aspect,uv.y-.20)/.68;
      float stone=strata(p);
      float ridge=sin(p.x*3.7+p.y*2.1+stone*5.4);
      float seams=smoothstep(.92,1.,abs(sin(p.x*7.3-p.y*3.1+stone*9.)));
      float flecks=hash(floor(p*950.));
      float grit=noise(p*195.);
      float rake=.5+.5*sin(p.x*16.4+p.y*8.7+stone*3.);
      float warmth=exp(-dot((p-vec2(-1.2,1.1))*vec2(.42,.56),(p-vec2(-1.2,1.1))*vec2(.42,.56)));
      float shade=.026+stone*.023+ridge*.004+grit*.009+flecks*.007+rake*.003-seams*.006;
      vec3 slate=vec3(.91,.85,.73)*shade;
      slate+=vec3(.035,.024,.012)*warmth;
      slate=mix(slate*.40,slate,(1.-smoothstep(.20,1.55,length(uv*vec2(.75,1.)))));
      vec3 beam=vec3(.045,.037,.023)*followLight(p);
      gl_FragColor=vec4(mix(quiet+beam*.3,slate*stageLight+beam,background),1.);
    }`;

  function localOffset(x,y,g0,g1,g2,g3,time,amount) {
    const tau=6.28318530718;
    const eddyX=Math.sin(y*15+time*.33)*Math.cos(x*9-time*.17);
    const eddyY=-Math.sin(x*15-time*.28)*Math.cos(y*9+time*.21);
    const driftX=Math.sin(time*(.42+.45*g2)+g0*tau)*Math.cos(time*.17+g1*tau);
    const driftY=Math.cos(time*(.36+.40*g3)+g1*tau)*Math.sin(time*.19+g0*tau);
    const fineX=Math.sin(time*1.31+g2*tau),fineY=Math.cos(time*1.13+g3*tau);
    return [.0176*amount*(.30*eddyX+.50*driftX+.20*fineX),.0176*amount*(.30*eddyY+.50*driftY+.20*fineY)];
  }
  function radiationOffset(x,y,z,g0,g1,g2,g3,time,amount,normal=[0,0,1],fineOnly=false) {
    if(fineOnly&&(g2>=.64||g1>=.16))return{offset:[0,0,0],alpha:1,chosen:0};
    if(amount<.0001)return{offset:[0,0,0],alpha:1,chosen:0};
    const smooth=(a,b,x)=>{const t=Math.max(0,Math.min(1,(x-a)/(b-a)));return t*t*(3-2*t);};
    const clamp=x=>Math.max(0,Math.min(1,x)),fract=x=>x-Math.floor(x);
    const selector=fract(g0*37.17+g2*17.71);
    const chosen=selector<=amount*.40?1:0;
    if(!chosen)return{offset:[0,0,0],alpha:1,chosen:0};
    const phase=fract(time/(2.8+g2*1.6)+g1*.754877666+g3*.569840296);
    const age=clamp(phase/.94),reach=.06+.19*amount;
    const life=smooth(0,.04,phase)*(1-smooth(.08,.94,phase));
    const length=Math.hypot(...normal);
    const n=length<.001?[0,0,1]:normal.map(v=>v/length);
    return{offset:n.map(v=>v*reach*age),alpha:life,chosen:1};
  }

  // CPU mirror used for snapshots: deform source and destination separately,
  // then run the existing morph and mix their alpha using its eased progress.
  function storyLoss(point,loss,grainSeed,fit=[1,0]) {
    const clamp=x=>Math.max(0,Math.min(1,x));
    const smooth=(a,b,x)=>{const t=clamp((x-a)/(b-a));return t*t*(3-2*t);};
    const amount=clamp(loss);
    if(amount<=0)return {point:[point[0],point[1],point[2]],alpha:1};
    const scale=Math.max(.00001,fit[0]),mask=point[2]/scale>=.026?1:0;
    const age=smooth(.10*grainSeed,.72+.28*grainSeed,amount),travel=mask*age*(.32+.68*age);
    return {point:[point[0]+(-.025-.045*grainSeed)*travel*scale,point[1]+(-.080-.120*grainSeed)*travel*scale,point[2]],alpha:1-.97*mask*age};
  }

  function rotateObject(point,angle) {
    const c=Math.cos(angle),s=Math.sin(angle);
    return[c*point[0]-s*point[1],s*point[0]+c*point[1],point[2]];
  }

  window.CourseOpeningMaterials=Object.freeze({gemFraction,mineralKind,vertex,fragment,backgroundVertex,backgroundFragment,localOffset,radiationOffset,storyLoss,rotateObject});
})();
