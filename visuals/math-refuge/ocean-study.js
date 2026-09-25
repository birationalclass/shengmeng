import * as THREE from 'three';
import {createOceanLayer} from '../ocean/ocean-renderer.js?v=refuge-ocean-1';
import {seaDepthGLSL} from './sea-depth.js?v100-reef';
import {BUILDING_SCALE as S} from './site-layout.js';

// The simulation stays in the original Ocean Study coordinates. Only its
// geographic embedding, bathymetry and lighting are adapted to the campus.
import {OCEAN_ORIGIN,findShore} from './coastal-site.js?v=refuge-ocean-1';

function createActiveCampusOcean(renderer,scene,water){
 const layer=createOceanLayer(renderer),root=new THREE.Group();root.name='Ocean Study · original breaking surf';
 const matrix=new THREE.Matrix4().set(-.94,0,-.341174,88, 0,1,0,OCEAN_ORIGIN[1], .341174,0,-.94,-35, 0,0,0,1);
 const inverse=matrix.clone().invert(),shore=new Float32Array(256*4);
 for(let i=0;i<256;i++){const a=-45+i/255*160,z=(a-35)/S,x=findShore(z);shore[i*4]=x===null?3.4:88-x*S;shore[i*4+3]=1;}
 const shoreTexture=new THREE.DataTexture(shore,256,1,THREE.RGBAFormat,THREE.FloatType);shoreTexture.minFilter=shoreTexture.magFilter=THREE.LinearFilter;shoreTexture.needsUpdate=true;
 const uniforms={studyMatrix:{value:matrix},studyView:{value:new THREE.Matrix4()},studyCamera:{value:new THREE.Vector3()},studyShore:{value:shoreTexture},studySun:{value:new THREE.Vector3()},studySky:water.skyMap,studyNight:water.nightVisibility};
 Object.assign(layer.uniforms,uniforms);Object.assign(layer.foamUniforms,uniforms);
 const lighting={studyCloud:water.skyCloudMap,studyCloudPrevious:water.skyCloudPrevious,studyCloudBlend:water.skyCloudBlend,studyCloudEnabled:water.skyCloudEnabled,studyReflection:water.reflectionDetail,studySunReflection:water.sunReflection,studySunStrength:water.sunStrength};
 Object.assign(layer.uniforms,lighting);Object.assign(layer.foamUniforms,lighting);
 const geography=`uniform mat4 studyMatrix,studyView;uniform vec3 studyCamera,studySun;uniform sampler2D studyShore,studySky;uniform float studyNight;
 ${seaDepthGLSL}
 vec2 studyPlan(vec2 ca){return vec2(88.-ca.x,ca.y-35.)/${S.toFixed(9)};}
 float studyMask(vec2 ca){vec2 p=studyPlan(ca);return smoothstep(.01,.15,beachMask(p))*(1.-smoothstep(1.4,3.4,seaDepthAt(p)));}
 `;
 function adapt(shader,isFragment=false,isFoam=false){
  shader=shader.replaceAll('cameraPosition','studyCamera').replaceAll('viewMatrix','studyView');
  shader=shader.replace('float shore(float a){return 3.4+1.4*sin(a*.023)+.38*sin(a*.093);}','float shore(float a){return texture2D(studyShore,vec2(clamp((a+45.)/160.,0.,1.),.5)).r;}');
  shader=shader.replace('float beachHeight(vec2 ca){return (ca.x-shore(ca.y))*.055+.012*noise(ca*.7);}','float beachHeight(vec2 ca){return -seaDepthAt(studyPlan(ca));}');
  shader=shader.replace(/vec3 sunDirection\(\)\{[^}]*\}/,'vec3 sunDirection(){return normalize(studySun);}');
  shader=shader.replace(/vec3 sky\(vec3 rd,bool clouds\)\{[\s\S]*?\n\}\n(?=vec3 tone)/,`vec3 sky(vec3 rd,bool clouds){vec3 d=normalize(mat3(studyMatrix)*rd);d.y=max(.002,d.y);vec2 uv=vec2(.5+atan(d.z,d.x)/6.2831853,sqrt(clamp(asin(d.y)/1.5707963,0.,1.)));return texture2D(studySky,uv).rgb+vec3(.002,.004,.009)*(1.-studyNight);}\n`);
  shader=shader.replace('return texture2D(studySky,uv).rgb+vec3(.002,.004,.009)*(1.-studyNight);','vec3 skyColor=texture2D(studySky,uv).rgb+vec3(.002,.004,.009)*(1.-studyNight);if(clouds&&studyReflection>.5){vec4 c=mix(texture2D(studyCloudPrevious,uv),texture2D(studyCloud,uv),studyCloudBlend);skyColor=skyColor*(1.-c.a*studyCloudEnabled)+c.rgb*studyCloudEnabled;}return skyColor;');
  if(!isFoam&&isFragment){
   shader=shader.replace(/vec3 tone\(vec3 x\)\{[^}]*\}/,'vec3 tone(vec3 x){return x;}');
   const end=shader.lastIndexOf('}');shader=shader.slice(0,end)+'\n#include <tonemapping_fragment>\n#include <colorspace_fragment>\n'+shader.slice(end);
   if(shader.includes('varying vec2 vCA'))shader=shader.replace('void main(){','void main(){if(studyMask(vCA)<.01)discard;');
   shader=shader.replace('float depth=(coast-vCA.x)*.18;','float depth=max(0.,-beachHeight(vCA));');
   shader=shader.replace('vec3 col=mix(body,reflection,fresnel*.87);','vec3 col=mix(body,reflection,fresnel);');
   shader=shader.replace('col+=light*min(14.,spec*sf*.24)*smoothstep(-4.,1.,uSun);','col+=light*min(14.,spec*sf*.24)*studySunStrength*studySunReflection;');
   shader=shader.replace('gl_FragColor=vec4(tone(col),coverage);','gl_FragColor=vec4(tone(col),coverage*studyMask(vCA));');
   shader=shader.replace('gl_FragColor=vec4(tone(col),opacity);','gl_FragColor=vec4(tone(col),opacity*studyMask(vCA));');
   // Beer–Lambert transmission uses the site's sand colour and actual depth.
   shader=shader.replace('vec3 sand=mix(vec3(.19,.14,.10),vec3(.43,.34,.22),day);','vec3 sand=vec3(.34,.285,.19)*(.3+.7*studyNight);');
   shader=shader.replace('body=mix(sand,body,1.-exp(-max(0.,waterThickness)*2.8));','vec3 transmittance=exp(-vec3(.43,.17,.085)*max(0.,waterThickness));body=sand*transmittance+body*(1.-transmittance);');
  }
  if(!isFragment){
   shader=shader.replace('vOpacity*=smoothstep(.45,1.8,gl_PointSize);','vOpacity*=smoothstep(.45,1.8,gl_PointSize)*studyMask(ca);');
   shader=shader.replace('*.25*step(.03,y);','*.25*step(.03,y)*studyMask(ca);');
  }
  return 'uniform sampler2D studyCloud,studyCloudPrevious;uniform float studyCloudBlend,studyCloudEnabled,studyReflection,studySunReflection,studySunStrength;\n'+geography+shader;
 }
 for(const mesh of [...layer.scene.children]){
  if(mesh===layer.water)mesh.renderOrder=1;
  mesh.material.vertexShader=adapt(mesh.material.vertexShader);mesh.material.fragmentShader=adapt(mesh.material.fragmentShader,true);
  mesh.onBeforeRender=(_r,_s,camera)=>{uniforms.studyView.value.multiplyMatrices(camera.matrixWorldInverse,matrix);uniforms.studyCamera.value.copy(camera.position).applyMatrix4(inverse);};root.add(mesh);
 }
 for(const mesh of layer.foamScene.children){mesh.material.vertexShader=adapt(mesh.material.vertexShader,false,true);mesh.material.fragmentShader=adapt(mesh.material.fragmentShader,true,true);}
 scene.add(root);
 const drawSize=new THREE.Vector2();let enabled=true;
 return {layer,root,inverse,
  setEnabled(value){enabled=value;root.visible=value;},
  update(camera,dt){if(!enabled)return;layer.camera=camera;const w=water;layer.uniforms.uViewportHeight.value=renderer.getDrawingBufferSize(drawSize).y;
   uniforms.studySun.value.copy(w.sunDirection.value).transformDirection(inverse);
   const target=renderer.getRenderTarget(),auto=renderer.autoClear;renderer.autoClear=true;
   try{layer.draw({time:5.6+w.time.value,wave:.8+w.waveStrength.value*.65,wind:Math.round(Math.min(1,w.windSpeed.value*w.windWaves.value/14)*20)/20,sun:Math.asin(Math.max(-1,Math.min(1,w.sunDirection.value.y)))*180/Math.PI,quality:w.waterDetail.value>.5?'high':'low',scale:1},{render:false,updateCamera:false});}
   finally{renderer.setRenderTarget(target);renderer.autoClear=auto;}
  },
  dispose(){const geometries=new Set();root.traverse(o=>{if(o.geometry)geometries.add(o.geometry);o.material?.dispose();});for(const g of geometries)g.dispose();for(const o of layer.foamScene.children){o.geometry.dispose();o.material.dispose();}layer.foamA.dispose();layer.foamB.dispose();layer.uniforms.uProfile.value.dispose();shoreTexture.dispose();scene.remove(root);}
 };
}

// Allocate the million-triangle surf and foam buffers only after a successful
// lightweight frame-rate trial (or an explicit manual selection).
export function createCampusOcean(renderer,scene,water){
 const empty=new THREE.DataTexture(new Uint8Array(4),1,1);empty.needsUpdate=true;
 const foam={value:empty},placeholder=new THREE.Group();let current=null,enabled=false,wasActive=false;
 return {
  get root(){return current?.root||placeholder;},get initialized(){return current!==null;},foam,
  setEnabled(value){
   enabled=Boolean(value);
   if(enabled&&!current){current=createActiveCampusOcean(renderer,scene,water);current.layer.lastTime=5.6+water.time.value;}
   current?.setEnabled(enabled);
   if(!enabled){wasActive=false;water.oceanStudy.value=0;}
  },
  update(camera,dt){
   if(!enabled||!current)return;
   // Resuming starts at today's sea time: no simulation catch-up or 96-pass prewarm.
   if(!wasActive){current.layer.lastTime=5.6+water.time.value;current.layer.foamAccumulator=0;}
   wasActive=true;current.update(camera,dt);foam.value=current.layer.uniforms.uFoam.value;water.oceanStudy.value=1;
  },
  dispose(){current?.dispose();empty.dispose();}
 };
}
