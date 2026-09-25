import * as THREE from 'three';
import {EllipticRenderer} from '../ocean/elliptic-renderer.js';
import {distanceSampler} from '../ocean/beach-navigation.js';
import {bedHeight} from '../ocean/elliptic-model.js';
import {makeWaveSpectrum} from '../ocean/wave-spectrum.js';
import {CAMPUS_ANCHOR,COAST_LIFT,toBeach,toMathCoordinates} from './elliptic-site.js?v=true-north-coast-1';

// One implementation of 01, embedded rigidly in the campus's physical metre frame.
export async function createCampusOcean(renderer,scene,water){
 const field=await new THREE.TextureLoader().loadAsync(new URL('../ocean/elliptic-distance.png',import.meta.url).href);
 field.flipY=false;field.colorSpace=THREE.NoColorSpace;field.minFilter=field.magFilter=THREE.LinearFilter;field.generateMipmaps=false;
 const sample=distanceSampler(field.image),layer=new EllipticRenderer(null,field,{renderer,sky:false});
 const matrix=new THREE.Matrix4().set(1,0,0,CAMPUS_ANCHOR-2000, 0,1,0,COAST_LIFT, 0,0,1,0, 0,0,0,1);
 const inverse=matrix.clone().invert(),rotation=new THREE.Quaternion().setFromRotationMatrix(inverse);
 const root=new THREE.Group();root.name='01 · elliptic coast · main hall (2 km, 0 km)';
 const uniforms={studyView:{value:new THREE.Matrix4()},studyCamera:{value:new THREE.Vector3()},studySun:{value:new THREE.Vector3()},studyMatrix:{value:matrix},studySky:water.skyMap,studyNight:water.nightVisibility,studyCloud:water.skyCloudMap,studyCloudPrevious:water.skyCloudPrevious,studyCloudBlend:water.skyCloudBlend,studyCloudEnabled:water.skyCloudEnabled,studyReflection:water.reflectionDetail};
 uniforms.studySunReflection=water.sunReflection;uniforms.studySunStrength=water.sunStrength;
 Object.assign(layer.uniforms,uniforms);
 const header='uniform mat4 studyView,studyMatrix;uniform vec3 studyCamera,studySun;uniform sampler2D studySky,studyCloud,studyCloudPrevious;uniform float studyNight,studyCloudBlend,studyCloudEnabled,studyReflection;\n';
 const materials=new Set([layer.waterNear,layer.waterFar,...layer.scene.children.map(o=>o.material)]);
 for(const material of materials){
  for(const key of ['vertexShader','fragmentShader']){
   let shader=material[key].replaceAll('cameraPosition','studyCamera').replaceAll('viewMatrix','studyView');
   shader=shader.replace('col+=light*min(18.,distribution*sf*gv*gl/(4.*nv))*smoothstep(-4.,1.,uSun);','col+=light*min(18.,distribution*sf*gv*gl/(4.*nv))*smoothstep(-4.,1.,uSun)*studySunReflection*studySunStrength;');
   shader=shader.replace(/vec3 sunDirection\(\)\{[^}]*\}/,'vec3 sunDirection(){return normalize(studySun);}');
   shader=shader.replace(/vec3 sky\(vec3 rd,bool clouds\)\{[\s\S]*?\n\}\n(?=vec3 tone)/,`vec3 sky(vec3 rd,bool clouds){vec3 d=normalize(mat3(studyMatrix)*rd);d.y=max(.002,d.y);vec2 uv=vec2(.5+atan(d.z,d.x)/6.2831853,sqrt(clamp(asin(d.y)/1.5707963,0.,1.)));vec3 col=texture2D(studySky,uv).rgb;if(clouds&&studyReflection>.5){vec4 c=mix(texture2D(studyCloudPrevious,uv),texture2D(studyCloud,uv),studyCloudBlend);col=col*(1.-c.a*studyCloudEnabled)+c.rgb*studyCloudEnabled;}return col+vec3(.002,.004,.009)*(1.-studyNight);}\n`);
   if(key==='fragmentShader'){
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
 let time=7.1,quality=2,lastWind=-1;
 return {root,settings,initialized:true,foam:{value:empty},
  setEnabled(){root.visible=true;},setQuality(level){quality=level;},
  ground(x,z){const p=toBeach(x,z);return bedHeight(sample(...p),...p)+COAST_LIFT;},
  update(camera,dt){
   if(!settings.paused)time+=Math.max(0,Math.min(.1,dt));
   const wind=Math.round(Math.min(1,water.windSpeed.value*water.windWaves.value/14)*20)/20;
   if(wind!==lastWind){lastWind=wind;makeWaveSpectrum(wind).forEach((w,i)=>{layer.uniforms.uWaves.value[i].set(w.x,w.z,w.k,w.amplitude);layer.uniforms.uPhases.value[i].set(w.omega,w.phase);});layer.uniforms.uWind.value=wind;}
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
