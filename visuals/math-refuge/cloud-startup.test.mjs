import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import * as T from '../3d/vendor/three.module.js';
let source=readFileSync(new URL('./volumetric-clouds.js',import.meta.url),'utf8');
source=source.replace("from './cloud-coverage.js'",`from '${new URL('./cloud-coverage.js',import.meta.url).href}'`).replace("from 'three'",`from '${new URL('../3d/vendor/three.module.js',import.meta.url).href}'`).replace("from './graphics-settings.js?v84-display'",`from '${new URL('./graphics-settings.js',import.meta.url).href}'`);
const {createVolumetricClouds}=await import('data:text/javascript;base64,'+Buffer.from(source).toString('base64'));
let current=null,compiled=0,uploads=0;const slices=[];
const renderer={isWebGLRenderer:true,extensions:{has:()=>false},initTexture(){uploads++;},async compileAsync(){compiled++;},initRenderTarget(){},getRenderTarget:()=>current,setRenderTarget:t=>current=t,render(){slices.push({height:current.scissor.w,total:current.height});}};
const cloud=createVolumetricClouds(renderer,{noiseSize:4});await cloud.prepare();assert.equal(compiled,1);assert.equal(uploads,1);
const u={cloudOrigin:{value:new T.Vector3()},cloud:{value:.5},sunPosition:{value:new T.Vector3(0,1,0)},sunColor:{value:new T.Color()},day:{value:1},storm:{value:0},cloudOffset:{value:new T.Vector2()},useVolumeClouds:{value:0},cloudBlend:{value:0},cloudMap:{value:null},cloudMapPrevious:{value:null}};
for(let i=0;i<15;i++){cloud.update(u,i*16);assert.equal(u.cloudMap.value,null,'incomplete initial panorama must not publish');}
cloud.update(u,240);assert(u.cloudMap.value);assert.equal(slices.length,16);assert(slices.every(s=>s.height<=s.total/16));
const visible=u.cloudMap.value;const before=slices.length;u.day.value=.9;
cloud.update(u,256);assert.equal(slices.length,before+1,'next panorama starts during the current blend');
for(let i=1;i<15;i++){cloud.update(u,256+i*16);assert.equal(u.cloudMap.value,visible,'partial panorama stays hidden');}
cloud.update(u,496);assert.notEqual(u.cloudMap.value,visible);assert.equal(u.cloudMapPrevious.value,visible,'prior complete image stays available for blending');
const old=u.cloudMap.value;cloud.setQuality('high');for(let i=0;i<15;i++){cloud.update(u,1000+i*16);assert.equal(u.cloudMap.value,old,'quality changes preserve the previous panorama');}
cloud.update(u,1240);assert.notEqual(u.cloudMap.value,old);assert.equal(current,null,'offscreen rendering restores prior target');cloud.dispose();
console.log('PASS cloud shader warmup, bounded initial/quality-change tiles and atomic panorama publication');
