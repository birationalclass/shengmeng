import * as THREE from 'three';
import {EllipticRenderer} from '../ocean/elliptic-renderer.js?v=horizon-depth-1';
import {distanceSampler} from '../ocean/beach-navigation.js';
import {bedHeight} from '../ocean/elliptic-model.js';
import {makeWaveSpectrum} from '../ocean/wave-spectrum.js';
import {CAMPUS_ANCHOR,COAST_LIFT,toBeach,toMathCoordinates} from './elliptic-site.js?v=true-north-coast-1';

// One implementation of 01, embedded rigidly in the campus's physical metre frame.
export async function createCampusOcean(renderer,scene,water){
 const field=await new THREE.TextureLoader().loadAsync(new URL('../ocean/elliptic-distance.png',import.meta.url).href);
 field.flipY=false;field.colorSpace=THREE.NoColorSpace;field.minFilter=field.magFilter=THREE.LinearFilter;field.generateMipmaps=false;
 const sample=distanceSampler(field.image),layer=new EllipticRenderer(null,field,{renderer,sky:false,backgroundOrder:1001});
 const matrix=new THREE.Matrix4().set(1,0,0,CAMPUS_ANCHOR-2000, 0,1,0,COAST_LIFT, 0,0,1,0, 0,0,0,1);
 const inverse=matrix.clone().invert(),rotation=new THREE.Quaternion().setFromRotationMatrix(inverse);
 const root=new THREE.Group();root.name='01 · elliptic coast · main hall (2 km, 0 km)';
 const uniforms={studyView:{value:new THREE.Matrix4()},studyCamera:{value:new THREE.Vector3()},studySun:{value:new THREE.Vector3()},studyMatrix:{value:matrix},studySky:water.skyMap,studySkyPrevious:(water.skyPrevious??={value:water.skyMap.value}),studySkyBlend:(water.skyBlend??={value:1}),studyMotion:{value:new THREE.Vector2()},studyFrameDelta:{value:1/60},studyNight:water.nightVisibility,studyCloud:water.skyCloudMap,studyCloudPrevious:water.skyCloudPrevious,studyCloudBlend:water.skyCloudBlend,studyCloudEnabled:water.skyCloudEnabled,studyReflection:water.reflectionDetail};
 uniforms.studySunReflection=water.sunReflection;uniforms.studySunStrength=water.sunStrength;
 Object.assign(layer.uniforms,uniforms);

 const header='uniform mat4 studyView,studyMatrix;uniform vec3 studyCamera,studySun;uniform sampler2D studySky,studySkyPrevious,studyCloud,studyCloudPrevious;uniform vec2 studyMotion;uniform float studySkyBlend,studyFrameDelta;uniform float studyNight,studyCloudBlend,studyCloudEnabled,studyReflection;\n';
 const materials=new Set([layer.waterNear,layer.waterFar,...layer.scene.children.map(o=>o.material)]);
 for(const material of materials){
  for(const key of ['vertexShader','fragmentShader']){
   let shader=material[key].replaceAll('cameraPosition','studyCamera').replaceAll('viewMatrix','studyView');
   shader=shader.replaceAll('col+=light*min(18.,distribution*sf*gv*gl/(4.*nv))*smoothstep(-4.,1.,uSun);','float solarHighlight=distribution*sf*gv*gl/(4.*nv);col+=light*(1.05*solarHighlight/(1.05+solarHighlight))*smoothstep(-4.,1.,uSun)*studySunReflection*studySunStrength;');
   shader=shader.replace(/vec3 sunDirection\(\)\{[^}]*\}/,'vec3 sunDirection(){return normalize(studySun);}');
   shader=shader.replace(/vec3 sky\(vec3 rd,bool clouds\)\{[\s\S]*?\n\}\n(?=vec3 tone)/,`vec3 sky(vec3 rd,bool clouds){vec3 d=normalize(mat3(studyMatrix)*rd);d.y=max(.002,d.y);vec2 uv=vec2(.5+atan(d.z,d.x)/6.2831853,sqrt(clamp(asin(d.y)/1.5707963,0.,1.)));vec3 col=mix(texture2D(studySkyPrevious,uv).rgb,texture2D(studySky,uv).rgb,studySkyBlend);if(clouds&&studyReflection>.5){vec4 c=mix(texture2D(studyCloudPrevious,uv),texture2D(studyCloud,uv),studyCloudBlend);col=col*(1.-c.a*studyCloudEnabled)+c.rgb*studyCloudEnabled;}return col+vec3(.012,.016,.025)*(1.-smoothstep(-10.,0.,uSun));}\n`);
   if(key==='fragmentShader'){
    // Scattering needs incident light. The standalone study's fixed teal
    // night floor made both the refracted bed and distant water self-luminous.
    // Keep the daytime response; fade continuously through nautical twilight.
    shader=shader.replaceAll('mix(vec3(.014,.092,.105),vec3(.025,.24,.255),day)',
      'mix(vec3(.009,.012,.018),mix(vec3(.014,.092,.105),vec3(.025,.24,.255),day),smoothstep(-10.,4.,uSun))');
    shader=shader.replace('vec3 ambient=mix(vec3(.22,.28,.38),vec3(.48,.64,.78),day);',
      'vec3 ambient=mix(vec3(.050,.055,.065),mix(vec3(.22,.28,.38),vec3(.48,.64,.78),day),smoothstep(-10.,4.,uSun));');
    // Evaluate normals in fixed world coordinates, not on the camera-following
    // adaptive vertices. Preserve unresolved slope energy as roughness.
    shader=shader.replace('n=normalize(vNormal)','n=vec3(0.,1.,0.)');
    shader=shader.replace('vec2 gravitySlope=vec2(0.);','vec2 gravitySlope=vec2(0.);float unresolvedSlope=0.;');
    shader=shader.replace('for(int i=16;i<32;i++)','for(int i=0;i<32;i++)');
    shader=shader.replace('float visible=1.-smoothstep(.8,3.,fwidth(phase));',`float travel=abs(dot(studyMotion,w.xy)*w.z)+studyFrameDelta*abs(uPhases[i].x);
      float visible=(1.-smoothstep(.45,2.,fwidth(phase)))*(1.-smoothstep(.4,2.,travel));
      unresolvedSlope+=.5*pow(w.z*w.w*uWave*1.7,2.)*(1.-visible*visible);`);

    // Filter capillary waves in time as well as space: unresolved frequencies
    // must not turn into alternating bright pixels during camera travel.
    shader=shader.replace('float visible=1.-smoothstep(.65,2.8,fwidth(phase));',
      'float visible=(1.-smoothstep(.45,2.,fwidth(phase)))*(1.-smoothstep(.35,2.2,studyFrameDelta*sqrt(9.81*k+.000074*k*k*k)));');
    shader=shader.replace('max(.00016,pow(.10+uWind*.06,4.)+variance*.22)','max(.0004,pow(.10+uWind*.06,4.)+variance*.5+unresolvedSlope*.5)');
    shader=shader.replace('nl=max(0.,sd.y),alpha2=.00016','nl=max(0.,sd.y),alpha2=.0045');

    // The campus atmospheric LUT excludes the solar disk. Subtracting the
    // standalone sky's disk here created a black reflected semicircle.
    shader=shader.replaceAll('reflected-=vec3(5.,3.75,1.85)*(1.-smoothstep(.009,.012,length(r-sd)))*(1.-dusk*.7);','');
    // Resolve short, broken breaker patches instead of repeated depth contours.
    shader=shader.replace('smoothstep(450.,1600.,distance)','smoothstep(120.,650.,distance)');
    shader=shader.replace('float band=pow(.5+.5*sin(shorePhase+noise(vCA*.016)*2.),3.);',`vec2 breakerUV=vCA+vec2(.21,-.08)*uTime;
      vec2 warp=vec2(noise(breakerUV*.035),noise(breakerUV*.047+17.))*9.;
      float pulse=pow(.5+.5*sin(shorePhase+noise(breakerUV*.08)*7.),8.);
      float islands=smoothstep(.48,.72,noise((breakerUV+warp)*.19));
      float band=pulse*islands*(.35+.65*noise(breakerUV*.61));`);
    // Foam reflects available light; it is not a white emissive layer at night.
    shader=shader.replace('vec3 white=mix(vec3(.65,.63,.57),vec3(.97,1.,.94),day);',
      'vec3 white=min(vec3(1.),sky(vec3(.2,.95,.12),false)*.65+vec3(.45,.42,.37)*smoothstep(-3.,10.,uSun));');
    // Break the uniform white film into advected, short-lived foam islands.
    shader=shader.replace('float foamPatch=smoothstep(.35,.70,noise(vCA*1.8+uTime*.18));',`vec2 foamUV=vCA+vec2(.24,-.11)*uTime;
       float foamPatch=smoothstep(.48,.72,noise(foamUV*.85+noise(foamUV*.13)*2.));
       foamPatch*=smoothstep(.22,.65,noise(foamUV*3.7));`);
    shader=shader.replace('float fine=(exp(-pow((waterThickness-.06)/.13,2.))*.45+crest*exp(-pow((waterThickness-.45)/.7,2.))*.2)*foamPatch;',
      'float fine=(exp(-pow((waterThickness-.055)/.09,2.))*.25+crest*exp(-pow((waterThickness-.35)/.45,2.))*.22)*foamPatch*(.3+.7*crest);');
    shader=shader.replace('float foam=band*exp(-pow((waterThickness-.45)/.7,2.))*.12*breakerLOD;',
      'float foam=band*exp(-pow((waterThickness-.45)/.7,2.))*.08*breakerLOD*smoothstep(.32,.68,noise(vCA*.08+uTime*.025));');
    shader=shader.replace(/vec3 tone\(vec3 x\)\{[^}]*\}/,'vec3 tone(vec3 x){return x;}');
    const end=shader.lastIndexOf('}');shader=shader.slice(0,end)+'\n#include <tonemapping_fragment>\n#include <colorspace_fragment>\n'+shader.slice(end);
   }
   material[key]='uniform float studySunReflection,studySunStrength;\n'+header+shader;
  }
  material.needsUpdate=true;
 }
 const qualityMaterials=[3,6,9].map((bands,level)=>[layer.waterNear,layer.waterFar].map(source=>{
  if(level===2)return source;
  const material=source.clone();material.uniforms=layer.uniforms;
  material.fragmentShader=material.fragmentShader.replace('i<9;i++','i<'+bands+';i++').replace('i<32;i++','i<'+(level===0?24:28)+';i++');
  materials.add(material);return material;
 }));
 layer.water.renderOrder=-100;
 for(const mesh of [...layer.scene.children]){mesh.frustumCulled=false;mesh.raycast=()=>{};root.add(mesh);}
 scene.add(root);
 const settings={tide:2.55,tidal:true,grid:false,paused:false},empty=new THREE.DataTexture(new Uint8Array(4),1,1);empty.needsUpdate=true;
 let time=7.1,quality=2,lastWind=-1,targetWaves=null,previousEye=null;
 return {root,settings,initialized:true,foam:{value:empty},
  setEnabled(){root.visible=true;},setQuality(level){quality=level;},
  ground(x,z){const p=toBeach(x,z);return bedHeight(sample(...p),...p)+COAST_LIFT;},
  update(camera,dt){
   if(previousEye)uniforms.studyMotion.value.set(camera.position.x-previousEye.x,camera.position.z-previousEye.z);
   else previousEye=camera.position.clone();
   previousEye.copy(camera.position);
   uniforms.studyFrameDelta.value+=(Math.max(1/240,Math.min(.1,dt))-uniforms.studyFrameDelta.value)*(1-Math.exp(-Math.max(0,dt)*4));
   if(!settings.paused)time+=Math.max(0,Math.min(.1,dt));
   const wind=Math.round(Math.min(1,water.windSpeed.value*water.windWaves.value/14)*20)/20;
   if(wind!==lastWind){lastWind=wind;targetWaves=makeWaveSpectrum(wind);}
   const windBlend=1-Math.exp(-Math.max(0,dt)/2);
   targetWaves.forEach((w,i)=>{const v=layer.uniforms.uWaves.value[i];v.w+=(w.amplitude-v.w)*windBlend;});
   layer.uniforms.uWind.value+=(wind-layer.uniforms.uWind.value)*windBlend;
   layer.camera.copy(camera);layer.camera.position.copy(camera.position).applyMatrix4(inverse);layer.camera.quaternion.copy(camera.quaternion).premultiply(rotation);
   uniforms.studyCamera.value.copy(layer.camera.position);uniforms.studySun.value.copy(water.sunDirection.value).transformDirection(inverse);
   layer.draw({time,tide:settings.tide,tidal:settings.tidal,wave:water.waveStrength.value*1.2,wind:.35,sun:Math.asin(Math.max(-1,Math.min(1,water.sunDirection.value.y)))*180/Math.PI,view:settings.grid?'plan':'aerial'},{render:false});
   uniforms.studyView.value.copy(layer.camera.matrixWorldInverse);
   if(camera.near!==layer.camera.near||camera.far!==layer.camera.far){camera.near=layer.camera.near;camera.far=layer.camera.far;camera.updateProjectionMatrix();}
   // Quality trims fine spray while retaining the same terrain, gravity waves and tide.
   if(quality<2)layer.uniforms.uFoamVisibility.value=0;
   layer.water.material=qualityMaterials[quality][layer.foamDetail?0:1];
   water.oceanLevel.value=layer.uniforms.uTide.value+COAST_LIFT;water.oceanStudy.value=1;
   renderer.domElement.dataset.coastCoordinates=toMathCoordinates(camera.position.x,camera.position.z).map(v=>v.toFixed(3)).join(',');
   renderer.domElement.dataset.coastTide=layer.uniforms.uTide.value.toFixed(2);
  },
  dispose(){root.traverse(o=>o.geometry?.dispose());for(const m of materials)m.dispose();field.dispose();empty.dispose();scene.remove(root);}
 };
}
