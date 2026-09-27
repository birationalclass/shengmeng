import test from 'node:test';
import assert from 'node:assert/strict';
import {fadeToward} from './effect-fade.js';
test('late effects never appear instantly during zero-time startup paints',()=>{
 assert.equal(fadeToward(0,1,0),0);assert.equal(fadeToward(.6,0,0),.6);
 let strength=0;
 for(let i=0;i<300;i++){const next=fadeToward(strength,1,1/60);assert(next>=strength&&next-strength<.015);strength=next;}
 assert(strength>.98&&strength<1);
 const next=fadeToward(strength,0,1/60);assert(next<strength&&strength-next<.015);
});
test('30 and 120 FPS fade at the same speed without overshoot',()=>{
 const simulate=fps=>{let value=0;for(let i=0;i<fps*3;i++)value=fadeToward(value,1,1/fps);return value;};
 assert(Math.abs(simulate(30)-simulate(120))<1e-12);
 assert(fadeToward(.7,0,3600)>.64,'Returning to focus cannot skip the fade');
});
test('real sky waits for the opening sun and fades atmosphere and cloud enable/disable',async()=>{
 const fs=await import('node:fs/promises'),T=await import('../3d/vendor/three.module.js');
 const urls=new Map();
 for(const file of ['sky-atmosphere.js','volumetric-clouds.js','deferred-textures.js','weather-sky.js']){
  let source=await fs.readFile(new URL(file,import.meta.url),'utf8');
  source=source.replace(/from '(\.\/[^']+)'/g,(_,path)=>`from '${urls.get(path.slice(2).split('?')[0])||new URL(path,import.meta.url).href}'`).replace("from 'three'",`from '${new URL('../3d/vendor/three.module.js',import.meta.url).href}'`);
  urls.set(file,'data:text/javascript;base64,'+Buffer.from(source).toString('base64'));
 }
 const {createWeatherSky}=await import(urls.get('weather-sky.js'));
 let target=null,focused=true;const calls=[];
 const renderer={isWebGLRenderer:true,autoClear:true,extensions:{has:()=>true},getRenderTarget:()=>target,setRenderTarget:t=>target=t,render:scene=>calls.push(scene.children[0].material.uniforms.sun.value.clone())};
 const sky=createWeatherSky({panorama:false,renderer,device:{startup:true,mobile:true,isRenderActive:()=>focused}}),u=sky.material.uniforms;
 assert.equal(calls.length,0,'Never precompute a noon sky before the opening clock is applied');
 const dawn=new T.Vector3(1,-.02,0).normalize();u.sunPosition.value.copy(dawn);sky.userData.updateAtmosphere(0);
 assert(calls[0].distanceTo(dawn)<1e-12);assert.equal(u.useAtmosphere.value,0);assert.equal(u.useVolumeClouds.value,0);
 sky.userData.updateAtmosphere(.05);assert(u.useAtmosphere.value>0&&u.useAtmosphere.value<.05);
 sky.userData.setCloudQuality('low');assert.equal(u.useVolumeClouds.value,0);
 sky.userData.updateAtmosphere(.05);const visible=u.useVolumeClouds.value;assert(visible>0&&visible<.05);
 sky.userData.setCloudQuality('off');assert.equal(u.useVolumeClouds.value,visible,'Disable retains a cached panorama during fade-out');
 sky.userData.updateAtmosphere(.05);assert(u.useVolumeClouds.value>0&&u.useVolumeClouds.value<visible);
 focused=false;const atmosphere=u.useAtmosphere.value,clouds=u.useVolumeClouds.value,count=calls.length;
 sky.userData.updateAtmosphere(5);assert.equal(u.useAtmosphere.value,atmosphere);assert.equal(u.useVolumeClouds.value,clouds);assert.equal(calls.length,count);
 sky.material.dispose();sky.geometry.dispose();
});
