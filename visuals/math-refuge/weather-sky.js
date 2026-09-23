import * as THREE from 'three';
export function createWeatherSky({panorama=true}={}){
 const fallback=new THREE.DataTexture(new Uint8Array([0,0,0,255]),1,1);fallback.needsUpdate=true;
 const uniforms={sunPosition:{value:new THREE.Vector3(1,.5,0)},sunColor:{value:new THREE.Color('#fff4df')},day:{value:1},warm:{value:0},direct:{value:1},cloud:{value:.12},storm:{value:0},twinkleTime:{value:0},clock:{value:0},radius:{value:.00465},showSun:{value:1},stars:{value:0},sidereal:{value:0},galaxyMap:{value:fallback},galaxyMix:{value:0}};
 const material=new THREE.ShaderMaterial({side:THREE.BackSide,depthWrite:false,uniforms,vertexShader:`varying vec3 ray;void main(){ray=position;vec4 p=projectionMatrix*mat4(mat3(viewMatrix))*modelMatrix*vec4(position,1.0);gl_Position=p.xyww;}`,fragmentShader:`
 uniform sampler2D galaxyMap;uniform float galaxyMix;
 precision highp float;varying vec3 ray;uniform vec3 sunPosition,sunColor;uniform float day,warm,direct,cloud,storm,clock,radius,showSun,stars,sidereal,twinkleTime;
 float hash(vec2 p){vec3 p3=fract(vec3(p.xyx)*.1031);p3+=dot(p3,p3.yzx+33.33);return fract((p3.x+p3.y)*p3.z);}
 float noise(vec2 p){vec2 i=floor(p),f=fract(p);f=f*f*(3.0-2.0*f);return mix(mix(hash(i),hash(i+vec2(1,0)),f.x),mix(hash(i+vec2(0,1)),hash(i+vec2(1,1)),f.x),f.y);}
 float fbm(vec2 p){float v=0.,a=.55;for(int i=0;i<4;i++){v+=a*noise(p);p=p*2.03+17.3;a*=.48;}return v;}
 // Fixed celestial coordinates: stars never re-randomize when time or weather changes.
 vec3 celestial(vec3 d){float a=sidereal,c=cos(a),s=sin(a);vec3 pole=normalize(vec3(0.,.518,-.855));return d*c+cross(pole,d)*s+pole*dot(pole,d)*(1.-c);}
 // An all-sky photographic field resolves the bulge, rifts, nebulae and stellar density.
 // This fixed orientation is an artistic sky, not a date-calibrated planetarium.
 vec3 nightStars(vec3 direction){vec3 d=celestial(direction);vec3 pole=normalize(vec3(.76,-.58,.30));vec3 axis=normalize(vec3(.30,0.,-.76));vec3 other=cross(pole,axis);vec3 g=vec3(dot(d,axis),dot(d,other),dot(d,pole));vec2 uv=vec2(.5+atan(g.y,g.x)/6.28318530718,.5+asin(clamp(g.z,-1.,1.))/3.14159265359);// Separate the broad galactic field from unresolved photographic star grain.
 vec3 field=texture2D(galaxyMap,uv).rgb;
 vec3 diffuse=texture2D(galaxyMap,uv,3.5).rgb;
 float haze=dot(diffuse,vec3(.2126,.7152,.0722));
 float peak=max(0.,dot(field-diffuse,vec3(.2126,.7152,.0722)));
 vec3 band=mix(vec3(haze),diffuse,.35)*(.30/(1.+2.*haze));
 // Keep only resolved bright stars; the millions of faint points merge into the band.
 vec3 bright=max(field-diffuse,vec3(0.))*smoothstep(.35,.70,peak)*.13;
 // Smooth celestial-space phases keep stars independent, even during accelerated time.
 float phase=dot(d,vec3(127.1,311.7,74.7));
 float shimmer=1.+.22*sin(twinkleTime*1.7+phase)+.10*sin(twinkleTime*2.9+phase*1.618);
 return (band+bright*shimmer)*galaxyMix;}

 void main(){vec3 d=normalize(ray);float y=max(d.y,0.0),horizon=pow(1.0-y,5.0);vec3 zenith=vec3(.014,.12,.43),edge=vec3(.32,.54,.80);vec3 clear=mix(zenith,edge,exp(-5.0*y));float facing=pow(max(dot(normalize(vec3(d.x,.001,d.z)),normalize(vec3(sunPosition.x,.001,sunPosition.z))),0.0),5.0);clear=mix(clear,vec3(.94,.32,.105),warm*horizon*facing*.78);vec3 night=mix(vec3(.0015,.003,.012),vec3(.006,.013,.027),horizon);vec3 color=mix(night,clear,day);color=mix(color,vec3(.33,.39,.47)*(.025+.975*day),cloud*storm*.68);
 if(stars>.0001)color+=nightStars(d)*stars*smoothstep(0.0,.18,d.y)*(1.-storm*.96);
 float angle=acos(clamp(dot(d,normalize(sunPosition)),-1.,1.));float edgeAA=max(fwidth(angle),.00004);float disk=1.0-smoothstep(radius-edgeAA,radius+edgeAA,angle);float limb=sqrt(max(0.0,1.0-pow(angle/radius,2.0)));float solar=showSun*smoothstep(-.002,.001,d.y); color+=sunColor*solar*(disk*(7.0+2.0*limb)+.18*exp(-pow(angle/.019,2.0)));
 vec2 uv=d.xz/max(d.y+.12,.12)*1.55+vec2(clock*.0025,clock*.0008);float n=fbm(uv),threshold=mix(.80,.22,cloud);float density=smoothstep(threshold-.07,threshold+.12,n)*smoothstep(-.015,.09,d.y);float shade=fbm(uv+vec2(.065,.035));vec3 white=mix(vec3(.58,.66,.75),vec3(1.28,1.30,1.32),smoothstep(.2,.7,shade));white=mix(white,vec3(.38,.43,.50),storm*.6);white=mix(white,vec3(.94,.47,.23),warm*facing*.48);white=mix(vec3(.002,.003,.005),white,day);color=mix(color,white,density*.97);
 gl_FragColor=vec4(max(color,vec3(0.0)),1.0);#include <tonemapping_fragment>
 #include <colorspace_fragment>
 }`.replace(';#include',';\n#include')});
 let disposed=false,loadedAt=0,panoramaTexture;
 if(panorama&&typeof window!=='undefined'&&typeof Image!=='undefined'){
  panoramaTexture=new THREE.TextureLoader().load(new URL('./assets/sky/eso0932a-6k.jpg',import.meta.url).href,texture=>{
   if(disposed){texture.dispose();return;}texture.colorSpace=THREE.SRGBColorSpace;texture.wrapS=THREE.RepeatWrapping;texture.minFilter=THREE.LinearMipmapLinearFilter;texture.magFilter=THREE.LinearFilter;texture.anisotropy=4;uniforms.galaxyMap.value=texture;loadedAt=performance.now();
  },undefined,()=>{ /* Keep the continuous dark sky when offline. */ });
 }
 material.addEventListener('dispose',()=>{disposed=true;fallback.dispose();panoramaTexture?.dispose();});
 const mesh=new THREE.Mesh(new THREE.SphereGeometry(1,48,24),material);mesh.onBeforeRender=()=>{uniforms.twinkleTime.value=performance.now()/1000;if(loadedAt)uniforms.galaxyMix.value=1-Math.exp(-(performance.now()-loadedAt)/1200);};mesh.name='Continuous Shanghai sky';mesh.frustumCulled=false;mesh.scale.setScalar(10000);return mesh;
}
