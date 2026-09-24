import {solarRefractionGLSL} from './solar-optics.js?v86-environment';
import * as THREE from 'three';
import {createVolumetricClouds} from './volumetric-clouds.js?v84-display';
import {createAtmosphereLUT} from './sky-atmosphere.js?v79-mobile';
export function createWeatherSky({panorama=true,renderer,device={},probe=false}={}){
 const fallback=new THREE.DataTexture(new Uint8Array([0,0,0,255]),1,1);fallback.needsUpdate=true;
 const atmosphere=createAtmosphereLUT(probe?null:renderer,device),volumeClouds=createVolumetricClouds(probe?null:renderer,device);
 const uniforms={nightStyle:{value:0},meteorEnabled:{value:1},starsEnabled:{value:1},cloudOrigin:{value:new THREE.Vector3(0,.015,0)},cloudBlend:{value:1},cloudMapPrevious:{value:volumeClouds?.texture||fallback},cloudMap:{value:volumeClouds?.texture||fallback},cloudOffset:{value:new THREE.Vector2()},useVolumeClouds:{value:volumeClouds?1:0},atmosphereMap:{value:atmosphere?.texture||fallback},useAtmosphere:{value:atmosphere?1:0},seaHorizon:{value:0},seaColor:{value:new THREE.Color('#8dbbdf')},sunPosition:{value:new THREE.Vector3(1,.5,0)},sunColor:{value:new THREE.Color('#fff4df')},day:{value:1},warm:{value:0},direct:{value:1},cloud:{value:.12},storm:{value:0},twinkleTime:{value:0},clock:{value:0},radius:{value:.00465},showSun:{value:1},stars:{value:0},sidereal:{value:0},galaxyMap:{value:fallback},galaxyMix:{value:0}};
 const material=new THREE.ShaderMaterial({side:THREE.BackSide,depthWrite:false,uniforms,vertexShader:`varying vec3 ray;void main(){ray=position;vec4 p=projectionMatrix*mat4(mat3(viewMatrix))*modelMatrix*vec4(position,1.0);gl_Position=p.xyww;}`,fragmentShader:`
 uniform sampler2D cloudMap,cloudMapPrevious;uniform float cloudBlend;uniform float useVolumeClouds;uniform vec2 cloudOffset;uniform sampler2D atmosphereMap;uniform float useAtmosphere;uniform sampler2D galaxyMap;uniform float galaxyMix;
 precision highp float;varying vec3 ray;uniform vec3 sunPosition,sunColor,seaColor;uniform float starsEnabled,nightStyle,meteorEnabled;uniform float seaHorizon;uniform float day,warm,direct,cloud,storm,clock,radius,showSun,stars,sidereal,twinkleTime;
 ${solarRefractionGLSL}
 float hash(vec2 p){vec3 p3=fract(vec3(p.xyx)*.1031);p3+=dot(p3,p3.yzx+33.33);return fract((p3.x+p3.y)*p3.z);}
 float noise(vec2 p){vec2 i=floor(p),f=fract(p);f=f*f*(3.0-2.0*f);return mix(mix(hash(i),hash(i+vec2(1,0)),f.x),mix(hash(i+vec2(0,1)),hash(i+vec2(1,1)),f.x),f.y);}
 float fbm(vec2 p){float v=0.,a=.55;for(int i=0;i<4;i++){v+=a*noise(p);p=p*2.03+17.3;a*=.48;}return v;}
 // Fixed celestial coordinates: stars never re-randomize when time or weather changes.
 vec3 celestial(vec3 d){float a=sidereal,c=cos(a),s=sin(a);vec3 pole=normalize(vec3(0.,.518,-.855));return d*c+cross(pole,d)*s+pole*dot(pole,d)*(1.-c);}
 // An all-sky photographic field resolves the bulge, rifts, nebulae and stellar density.
 // This fixed orientation is an artistic sky, not a date-calibrated planetarium.
 vec3 nightStars(vec3 direction){vec3 d=celestial(direction);vec3 pole=normalize(vec3(.76,-.58,.30));vec3 axis=normalize(vec3(.30,0.,-.76));vec3 other=cross(pole,axis);vec3 g=vec3(dot(d,axis),dot(d,other),dot(d,pole));vec2 uv=vec2(.5+atan(g.y,g.x)/6.28318530718,.5+asin(clamp(g.z,-1.,1.))/3.14159265359);// Separate the broad galactic field from unresolved photographic star grain.
 // Star-removed diffuse panorama; photographic bloom is never used as a point source.
 vec3 diffuse=texture2D(galaxyMap,uv).rgb;
 float haze=dot(diffuse,vec3(.2126,.7152,.0722));
 vec3 band=mix(vec3(haze),diffuse,mix(.65,1.15,nightStyle))*(mix(.68,1.8,nightStyle)/(1.+2.5*haze));
 vec2 grid=uv*vec2(160.,80.),cell=floor(grid);
 float latitude=cos((uv.y-.5)*3.14159265);
 vec2 metric=vec2(max(.025,latitude),1.);
 // Differentiate the continuous 3D direction, never wrapped longitude UVs.
 // Across the +/-pi seam, UV derivatives jump by a whole texture width.
 float pixel=max(length(fwidth(d))*.7071*(80./3.14159265),.0001);
 vec3 points=vec3(0.);
 for(int j=-1;j<=1;j++)for(int i=-1;i<=1;i++){
  vec2 neighbor=cell+vec2(float(i),float(j));
  vec2 key=vec2(mod(neighbor.x+160.,160.),neighbor.y);
  float seed=hash(key+13.7);
  if(seed>1.-.095*max(0.,latitude)&&neighbor.y>=0.&&neighbor.y<80.){
   vec2 center=neighbor+.16+.68*vec2(hash(key+37.1),hash(key+91.3));
   float distance=length((grid-center)*metric)/pixel;
   float magnitude=hash(key+51.9);
   // Gaussian pixel footprint: brightness varies, but stars never become resolved disks.
   float sigma=mix(.40,.60,pow(magnitude,4.));
   float core=exp(-.5*pow(distance/sigma,2.));
   float halo=exp(-.5*pow(distance/1.15,2.))*.025*pow(magnitude,6.);
   float phase=hash(key+77.)*6.2831853;
   float shimmer=1.+(.035+.045*(1.-max(direction.y,0.)))*(sin(twinkleTime*1.8+phase)+.25*sin(twinkleTime*3.1+phase*2.3));
   vec3 tint=mix(vec3(.78,.86,1.),vec3(1.,.90,.76),hash(key+19.));
   points+=tint*(core+halo)*mix(.045,.65,pow(magnitude,3.))*shimmer;
  }
 }
 float transmission=exp(-.10/max(.07,direction.y));
 return (band*galaxyMix+points)*transmission;}

 // Rare deterministic meteors: a short tapered trail, never a repeating shower.
 vec3 meteor(vec3 d,float pixel){
 float event=floor(twinkleTime/31.),age=mod(twinkleTime,31.)-4.-hash(vec2(event,7.))*12.;
 if(age<0.||age>1.5||meteorEnabled<.5)return vec3(0.);
 float az=hash(vec2(event,3.))*6.28318;
 vec3 start=normalize(vec3(cos(az),.8+hash(vec2(event,5.)),sin(az)));
 vec3 raw=cross(start,vec3(0.,1.,0.))*.8+vec3(0.,-.6,0.);
 vec3 tangent=normalize(raw-start*dot(raw,start)),plane=normalize(cross(start,tangent));
 float t=age/1.5,head=t*.30,along=atan(dot(d,tangent),dot(d,start));
 float across=asin(clamp(dot(d,plane),-1.,1.)),behind=head-along;
 float lengthTrail=min(.065,head),width=max(pixel*.55,.000035);
 float taper=clamp(1.-behind/max(lengthTrail,.00001),0.,1.);
 float trail=exp(-.5*pow(across/(width*(.35+.65*taper)),2.))*taper*taper;
 trail*=smoothstep(-width,width,behind)*(1.-smoothstep(lengthTrail-width,lengthTrail+width,behind));
 float core=exp(-.5*(across*across+behind*behind)/(width*width));
 float fade=smoothstep(0.,.12,t)*(1.-smoothstep(.65,1.,t));
 return vec3(.55,.65,.8)*(trail*.65+core)*fade;
 }
 void main(){vec3 d=normalize(ray);float angularPixel=max(length(dFdx(d)),length(dFdy(d)));float y=max(d.y,0.0),horizon=pow(1.0-y,5.0);vec3 zenith=vec3(.014,.12,.43),edge=vec3(.32,.54,.80);vec3 clear=mix(zenith,edge,exp(-5.0*y));float facing=pow(max(dot(normalize(vec3(d.x,.001,d.z)),normalize(vec3(sunPosition.x,.001,sunPosition.z))),0.0),5.0);clear=mix(clear,vec3(.94,.32,.105),warm*horizon*facing*.78);vec3 night=mix(vec3(.0015,.003,.012),vec3(.006,.013,.027),horizon);vec2 skyUV=vec2(.5+atan(d.z,d.x)/6.28318530718,sqrt(clamp(asin(clamp(d.y,0.,1.))/1.57079632679,0.,1.)));vec3 physical=texture2D(atmosphereMap,skyUV).rgb;vec3 color=mix(mix(night,clear,day),night*(1.-day)+physical,useAtmosphere);color=mix(color,vec3(.33,.39,.47)*(.025+.975*day),cloud*storm*.68);
 if(stars*starsEnabled>.0001)color+=(nightStars(d)+meteor(d,angularPixel))*stars*smoothstep(0.0,.18,d.y)*(1.-storm*.96);
 // Trace an apparent viewing ray back through the refracting atmosphere.
 vec3 solarRay=d;if(dot(d,normalize(sunPosition))>.97)solarRay=unrefractSunRay(d);
 // atan(cross,dot) remains stable at the disk centre; acos loses precision there.
 float angle=atan(length(cross(solarRay,normalize(sunPosition))),dot(solarRay,normalize(sunPosition)));float edgeAA=max(fwidth(angle),.00004);float disk=1.0-smoothstep(radius-edgeAA,radius+edgeAA,angle);float limb=sqrt(max(0.0,1.0-pow(angle/radius,2.0)));float horizonAA=max(fwidth(d.y),.000001);float aboveSea=smoothstep(-horizonAA,horizonAA,d.y);
 // Only the part actually below the sea horizon is occulted, in world-ray coordinates.
 // Once the full refracted disk clears the horizon no camera-dependent crop is applied.
 float solar=showSun*aboveSea; color+=sunColor*solar*(disk*(7.0+2.0*limb)+.18*exp(-pow(angle/.019,2.0)));
 vec4 cloudLight=mix(texture2D(cloudMapPrevious,skyUV),texture2D(cloudMap,skyUV),cloudBlend);color=color*(1.-cloudLight.a*useVolumeClouds)+cloudLight.rgb*useVolumeClouds;

 // The distant ocean meets the same horizontal ray used to clip the solar disk.
 // Below the horizon the same grazing sky radiance continues behind the finite ocean.
 // Never insert a fixed fog-colour strip here.
 // Continue the distant sea beyond the finite water mesh, retaining sea/sky contrast.
 float seaSide=1.-smoothstep(-max(fwidth(d.y),.00003),max(fwidth(d.y),.00003),d.y);
 color*=mix(vec3(1.),mix(vec3(.76,.84,.89),vec3(.94),storm),seaSide);
 gl_FragColor=vec4(max(color,vec3(0.0)),1.0);#include <tonemapping_fragment>
 #include <colorspace_fragment>
 }`.replace(';#include',';\n#include')});
 let disposed=false,loadedAt=0,panoramaTexture;
 if(panorama&&typeof window!=='undefined'&&typeof Image!=='undefined'){
  panoramaTexture=new THREE.TextureLoader().load(new URL('./assets/sky/galaxy-diffuse.jpg',import.meta.url).href,texture=>{
   if(disposed){texture.dispose();return;}texture.colorSpace=THREE.SRGBColorSpace;texture.wrapS=THREE.RepeatWrapping;texture.minFilter=THREE.LinearMipmapLinearFilter;texture.magFilter=THREE.LinearFilter;texture.anisotropy=4;uniforms.galaxyMap.value=texture;loadedAt=performance.now();
  },undefined,()=>{ /* Keep the continuous dark sky when offline. */ });
 }
 material.addEventListener('dispose',()=>{disposed=true;atmosphere?.dispose();volumeClouds?.dispose();fallback.dispose();panoramaTexture?.dispose();});
 const mesh=new THREE.Mesh(new THREE.SphereGeometry(1,48,24),material);mesh.onBeforeRender=(_r,_s,camera)=>{uniforms.cloudOrigin.value.copy(camera.position).multiplyScalar(.001);uniforms.cloudOrigin.value.y=Math.max(.001,uniforms.cloudOrigin.value.y);uniforms.twinkleTime.value=performance.now()/1000;if(loadedAt)uniforms.galaxyMix.value=1-Math.exp(-(performance.now()-loadedAt)/1200);};let cloudsEnabled=true;mesh.userData.setCloudQuality=level=>{cloudsEnabled=level!=='off';uniforms.useVolumeClouds.value=cloudsEnabled&&volumeClouds?1:0;if(cloudsEnabled)volumeClouds?.setQuality(level);};mesh.userData.updateAtmosphere=()=>{atmosphere?.update(uniforms.sunPosition.value,uniforms.cloud.value);if(cloudsEnabled)volumeClouds?.update(uniforms);};mesh.userData.updateAtmosphere();mesh.name='Continuous Shanghai sky';mesh.frustumCulled=false;mesh.scale.setScalar(10000);return mesh;
}
