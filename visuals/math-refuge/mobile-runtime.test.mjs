import test from 'node:test';
import assert from 'node:assert/strict';
import {mobilePolicy,withDeadline,fetchLocal,decodeImage} from './mobile-runtime.js';
import {displayProfile} from './display-profile.js';
import fs from 'node:fs/promises';
import * as T from '../3d/vendor/three.module.js';

test('iPhone and desktop-mode iPad retain mobile budgets in both orientations',()=>{
 for(const userAgent of ['iPhone','iPad','Macintosh'])for(const [width,height] of [[390,844],[844,390],[1366,1024]]){
  const p=mobilePolicy({width,height,userAgent,maxTouchPoints:5});
  assert(p.mobile&&p.ios);assert.equal(p.boardScale,.5);assert.equal(p.noiseSize,32);
  const d=displayProfile(width,height,3,'high',4,0,p);
  assert(d.direct);assert(d.pixelRatio<=2);assert(width*height*d.pixelRatio**2<=1200000.1);
 }
 const desktop=mobilePolicy({userAgent:'Macintosh',maxTouchPoints:0});
 assert(!desktop.mobile);assert.equal(desktop.boardScale,1);assert.equal(desktop.cloudSteps,24);
 const safe=mobilePolicy({safe:true}),d=displayProfile(430,932,3,'high',4,0,safe);
 assert(safe.mobile);assert(!d.shadows);assert(d.direct);assert(d.pixelRatio<=1.25);
 assert(430*932*d.pixelRatio**2<=650000.1);
});

test('startup deadlines reject hung resources and abort network work',async()=>{
 assert.equal(await withDeadline(Promise.resolve(7),10,'测试'),7);
 await assert.rejects(withDeadline(new Promise(()=>{}),5,'字体'),/字体超时/);
 const original=globalThis.fetch;
 let aborted=false;
 try{
  globalThis.fetch=(_,options)=>new Promise((_,reject)=>options.signal.addEventListener('abort',()=>{aborted=true;reject(new Error('aborted'));}));
  await assert.rejects(fetchLocal('/test',{timeout:5}),/资源加载超时/);assert(aborted);
  globalThis.fetch=async()=>({ok:false,status:404});
  await assert.rejects(fetchLocal('/test'),/404/);
 }finally{globalThis.fetch=original;}
});

test('Retina desktops bound pixels even when Safari has no GPU timer',()=>{
 for(const [width,height] of [[1280,720],[2240,1260],[2560,1440]]){
  const automatic=displayProfile(width,height,2,'high',4,4,{gpuTiming:true});
  const withoutTimer=displayProfile(width,height,2,'high',4,4,{gpuTiming:false});
  assert(width*height*automatic.pixelRatio**2<=4000000.1);
  assert(width*height*withoutTimer.pixelRatio**2<=2800000.1);
  assert(withoutTimer.shadows);assert.equal(withoutTimer.samples,4);
 }
 const desktop=mobilePolicy();assert.equal(desktop.cloudSize,512);assert.equal(desktop.cloudInterval,250);
});

test('an image that never decodes cannot leave entry waiting forever',async()=>{
 const original=globalThis.Image;let pending;
 try{
  globalThis.Image=class{constructor(){pending=this;}set src(value){this.url=value;}};
  await assert.rejects(decodeImage('/test',5),/图像加载超时/);
  assert.equal(pending.url,'');assert.equal(pending.onload,null);assert.equal(pending.onerror,null);
 }finally{globalThis.Image=original;}
});

test('mobile sky uses bounded targets, throttles updates and restores render state',async()=>{
 const load=async name=>{
  const source=(await fs.readFile(new URL(name,import.meta.url),'utf8')).replace(/from '(\.\/graphics-settings\.js)[^']*'/g,(_,path)=>`from '${new URL(path,import.meta.url).href}'`).replace("from 'three'",`from '${new URL('../3d/vendor/three.module.js',import.meta.url).href}'`);
  return import('data:text/javascript;base64,'+Buffer.from(source).toString('base64'));
 };
 const {createVolumetricClouds}=await load('./volumetric-clouds.js'),{createAtmosphereLUT}=await load('./sky-atmosphere.js');
 const policy=mobilePolicy({userAgent:'iPhone'}),originalTarget={name:'main'},calls=[];
 let current=originalTarget;
 const renderer={isWebGLRenderer:true,autoClear:false,extensions:{has:()=>true},getRenderTarget:()=>current,setRenderTarget:t=>{current=t;},render:scene=>calls.push({target:current,material:scene.children[0].material,scissor:current.scissor?.toArray()})};
 const cloud=createVolumetricClouds(renderer,policy),u={cloud:{value:.6},day:{value:1},storm:{value:0},sunPosition:{value:new T.Vector3(1,1,0).normalize()},cloudOffset:{value:new T.Vector2()},cloudOrigin:{value:new T.Vector3(0,.015,0)},sunColor:{value:new T.Color('white')},useVolumeClouds:{value:1},cloudBlend:{value:0},cloudMap:{},cloudMapPrevious:{}};
 cloud.update(u,0);assert.equal(calls.length,1);assert.equal(calls[0].target.width,256);assert.equal(calls[0].target.height,128);
 assert.equal(calls[0].material.uniforms.volume.value.image.width,32);assert.equal(calls[0].material.uniforms.marchSteps.value,16);
 u.cloudOffset.value.x+=.01;cloud.update(u,10);assert.equal(calls.length,1,'Sub-frame weather changes do not retrace clouds');
 const initial=cloud.texture;
 cloud.update(u,500);assert.equal(calls.length,2);assert.equal(cloud.texture,initial,'Never expose a partially drawn cloud texture');
 assert.deepEqual(calls[1].scissor,[0,0,256,64]);
 u.cloudOffset.value.x=.5;cloud.update(u,516);assert.equal(calls.length,3);assert.notEqual(cloud.texture,initial);
 assert.deepEqual(calls[2].scissor,[0,64,256,64]);assert.equal(calls[2].material.uniforms.offset.value.x,.01,'All strips use one frozen weather snapshot');
 assert.equal(u.cloudMapPrevious.value,initial);assert.equal(u.cloudBlend.value,0);
 cloud.update(u,700);assert.equal(calls.length,3,'Do not overwrite the old frame while it still participates in blending');
 assert.equal(current,originalTarget);assert.equal(renderer.autoClear,false);cloud.dispose();
 const atmosphere=createAtmosphereLUT(renderer,policy);atmosphere.update(u.sunPosition.value,.6);
 assert.equal(calls[3].target.width,128);assert.equal(calls[3].target.height,64);
 atmosphere.update(new T.Vector3(1,1,.01),.7);assert.equal(calls.length,4,'Atmosphere also respects its update interval');atmosphere.dispose();
 assert.equal(createVolumetricClouds(renderer,{safe:true}),null);assert.equal(createAtmosphereLUT(renderer,{safe:true}),null);
 renderer.extensions.has=()=>false;assert.equal(createAtmosphereLUT(renderer,policy),null);
 const compatible=createVolumetricClouds(renderer,policy);compatible.update(u);assert.equal(calls.at(-1).target.texture.type,T.UnsignedByteType);compatible.dispose();
 const desktop=createVolumetricClouds(renderer,{...policy,mobile:false});desktop.update(u,0);const published=desktop.texture,start=calls.length;
 u.cloudOffset.value.x+=1;
 for(let tile=0;tile<4;tile++){
  desktop.update(u,500+tile*16);
  assert.deepEqual(calls[start+tile].scissor,[0,tile*32,256,32]);
  if(tile<3)assert.equal(desktop.texture,published);
 }
 assert.notEqual(desktop.texture,published);assert.equal(current,originalTarget);desktop.dispose();
});
