/* Mineral grains, a shared perspective camera and a procedural slate stage.
 * No image textures: particles keep their seed and identity across every scene.
 * CPU offset helpers mirror shader trajectories for authoring and continuity checks.
 */
(() => {
  'use strict';
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
      return camera*vec3(-.30+.22*sin(time*.091),.48*sin(time*.113+.32),.045*sin(time*.073));
    }
    vec3 toCamera(vec3 p) {
      vec3 a=cameraAngles();return rotateZ(rotateX(rotateY(p,a.y),a.x),a.z);
    }
    vec3 fromCamera(vec3 p) {
      vec3 a=cameraAngles();return rotateY(rotateX(rotateZ(p,-a.z),-a.x),-a.y);
    }
    float cameraDistance() {return 3.9+.35*sin(time*.079+.8);}
    float cameraFit() {
      return min(.68,aspect*.84)*(1.+camera*(.065+.045*sin(time*.097-.5)));
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
    uniform float camera;
    uniform float radiation;
    uniform float colorAmount;
    uniform mediump float complexity;
    uniform mediump float depth;
    uniform float wander;
    varying mediump vec3 color;
    varying mediump float opacity;
    varying mediump vec4 material;
    ${cameraMath}

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

    // A minority of the same grains peel away. Each cycle returns to its origin
    // while invisible, so even interrupted transitions have no particle reset pop.
    vec4 escapeGrain(vec3 p) {
      float selector=fract(grain.x*37.17+grain.z*17.71);
      float chosen=(1.-smoothstep(radiation*.18-.006,radiation*.18,selector))*step(.0001,radiation);
      float phase=fract(time/(7.+grain.z*6.)+grain.y);
      float travel=smoothstep(.08,.78,phase)*(1.-smoothstep(.93,1.,phase));
      float life=smoothstep(0.,.13,phase)*(1.-smoothstep(.68,.95,phase));
      float angle=grain.w*6.28318530718;
      vec2 outward=normalize(p.xy+vec2(sin(angle),cos(angle))*.10+vec2(.0001));
      float reach=(.28+.82*radiation)*chosen;
      vec3 offset=vec3(
        outward.x*travel*(.65+.50*grain.z)+sin(time*.58+grain.y*6.28318530718)*travel*.10,
        outward.y*travel*(.65+.50*grain.z)+travel*travel*(.12+.25*grain.w),
        .13*travel+(.60+.65*grain.w)*travel*travel
      )*reach;
      return vec4(offset,mix(1.,life,chosen));
    }

    vec3 mineral(float selector) {
      if (selector < .26) return vec3(.20, .52, .38);
      if (selector < .49) return vec3(.24, .40, .70);
      if (selector < .73) return vec3(.83, .43, .25);
      return vec3(.90, .86, .72);
    }

    void main() {
      float t=progress;
      float e=t*t*t*(t*(t*6.-15.)+10.);
      vec2 delta=finish.xy-start.xy;
      float arch=sin(3.14159265359*e);
      vec3 p=mix(start,finish,e);
      p.xy+=vec2(-delta.y,delta.x)*arch*.28;
      float dist=length(delta);
      p.xy+=vec2(sin(grain.x*19.+e*6.283),cos(grain.y*23.-e*6.283))*
        arch*min(.022,dist*.16);
      p.xy+=localWander(p.xy);
      vec4 escaped=escapeGrain(p);
      p+=escaped.xyz;
      vec3 q=toCamera(p);
      float w=1.-camera*q.z/cameraDistance();
      float fit=cameraFit();
      // With camera=0 this is exactly the original flat XY framing. Z still
      // records true surface depth, allowing the near side of the torus to occlude.
      gl_Position=vec4(q.x*fit/aspect,q.y*fit+cameraCentre()*w,-q.z*.20,w);

      float variedSize=.64+1.02*grain.y;
      if(grain.z>.64)variedSize=1.50+.96*grain.y;
      if(grain.z>.94)variedSize=2.78+1.18*grain.y;
      float size=mix(1.45+.16*grain.z,variedSize,complexity);
      gl_PointSize=size*mix(1.,1.16,depth)*dpr*clamp(1./w,.68,1.65);

      vec3 n=mix(normalStart,normalFinish,e);
      if(length(n)<.001)n=vec3(0.,0.,1.);
      n=normalize(n);
      vec3 lamp=normalize(vec3(-.52,.64,.79));
      float diffuse=max(0.,dot(n,lamp));
      float macroLight=.32+.75*diffuse;
      float lampFalloff=.84+.16*clamp(1.-length(p.xy-vec2(-.35,.48))*.5,0.,1.);
      vec3 gold=mix(vec3(.46,.33,.16),vec3(.91,.77,.49),grain.w);
      gold=mix(gold,vec3(.99,.91,.74),pow(grain.y,18.)*.55);
      float selector=fract(grain.y*17.17+grain.z*31.31);
      vec3 tint=mineral(selector)*(.73+.27*grain.w);
      float coloured=(1.-smoothstep(colorAmount*.72-.012,colorAmount*.72,grain.x))*step(.001,colorAmount);
      color=mix(gold,tint,coloured)*macroLight*lampFalloff;
      vec3 eye=fromCamera(vec3(0.,0.,1.));
      float sheen=pow(max(0.,dot(n,normalize(lamp+eye))),24.);
      color+=vec3(.94,.78,.48)*sheen*.13;
      opacity=(.65+.30*grain.x)*(1.-complexity*step(.94,grain.z)*.10)*escaped.w;
      material=grain;
    }`;

  const fragment = `precision mediump float;
    uniform mediump float depth;
    uniform mediump float complexity;
    varying mediump vec3 color;
    varying mediump float opacity;
    varying mediump vec4 material;
    void main() {
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
      gl_FragColor=vec4(mix(flatColor,solidColor,depth),alpha);
    }`;

  const backgroundVertex = `attribute vec2 pos;varying vec2 uv;
    void main(){uv=pos;gl_Position=vec4(pos,1.,1.);}`;
  const backgroundFragment = `precision highp float;
    varying vec2 uv;
    uniform float aspect;
    uniform float time;
    uniform float camera;
    uniform float background;
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
      if(background<.0001){gl_FragColor=vec4(quiet,1.);return;}
      // Intersect the inverse camera ray with a world-space slate plane beneath
      // the particles. Its granular texture remains attached during every orbit.
      vec2 image=vec2(uv.x*aspect,uv.y-cameraCentre())/cameraFit();
      vec3 rayOrigin=fromCamera(vec3(image,0.));
      vec3 ray=fromCamera(vec3(-image*camera/cameraDistance(),1.));
      vec3 world=rayOrigin+ray*((-.68-rayOrigin.z)/max(.18,ray.z));
      vec2 p=world.xy;
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
      gl_FragColor=vec4(mix(quiet,slate,background),1.);
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
  function radiationOffset(x,y,z,g0,g1,g2,g3,time,amount) {
    if(amount<=0)return{offset:[0,0,0],alpha:1};
    const smooth=(a,b,x)=>{const t=Math.max(0,Math.min(1,(x-a)/(b-a)));return t*t*(3-2*t);};
    const fract=x=>x-Math.floor(x),tau=6.28318530718;
    const selector=fract(g0*37.17+g2*17.71);
    const chosen=(1-smooth(amount*.18-.006,amount*.18,selector))*(amount>=.0001?1:0);
    const phase=fract(time/(7+g2*6)+g1);
    const travel=smooth(.08,.78,phase)*(1-smooth(.93,1,phase));
    const life=smooth(0,.13,phase)*(1-smooth(.68,.95,phase));
    const angle=g3*tau,ox=x+Math.sin(angle)*.10+.0001,oy=y+Math.cos(angle)*.10+.0001;
    const length=Math.hypot(ox,oy),dx=ox/length,dy=oy/length,reach=(.28+.82*amount)*chosen;
    return {offset:[
      (dx*travel*(.65+.50*g2)+Math.sin(time*.58+g1*tau)*travel*.10)*reach,
      (dy*travel*(.65+.50*g2)+travel*travel*(.12+.25*g3))*reach,
      (.13*travel+(.60+.65*g3)*travel*travel)*reach
    ],alpha:1+(life-1)*chosen};
  }
  window.CourseOpeningMaterials=Object.freeze({vertex,fragment,backgroundVertex,backgroundFragment,localOffset,radiationOffset});
})();
