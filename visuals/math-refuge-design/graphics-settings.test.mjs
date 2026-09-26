import test from 'node:test';import assert from 'node:assert/strict';
import {recommendedGraphics,resolutionRatio,sunWaterVisibility} from './graphics-settings.js';
import {RenderBudget} from './render-budget.js';
import {configureCameraInput} from './camera-input.js';
import * as T from '../3d/vendor/three.module.js';
test('recommendation respects mobile limits and render size limits',()=>{
 assert.equal(recommendedGraphics({gpu:'RTX 3080 Ti',maxTextureSize:16384}).cloudQuality,'medium');
 assert.equal(recommendedGraphics({mobile:true,gpu:'RTX 3080 Ti',maxTextureSize:16384}).cloudQuality,'low');
 assert(resolutionRatio(3,150,3840,2160,8192)<=Math.sqrt(8500000/(3840*2160)));
});
test('reading protection never reduces selected resolution even under heavy GPU load',()=>{
 const b=new RenderBudget();for(let t=0;t<20000;t+=250){b.sample(28,t);b.update(t,{reading:true,protectText:true});}assert.equal(b.scale,1);
 const fast=new RenderBudget();for(let t=0;t<20000;t+=250){fast.sample(12,t);fast.update(t,{targetFPS:120});}assert(fast.scale<1);
});
test('solar reflection disappears continuously below the visible disk',()=>{
 assert.equal(sunWaterVisibility(-.03,.02),0);assert.equal(sunWaterVisibility(.03,.02),1);assert.equal(sunWaterVisibility(0,.02),.5);
 let prior=0;for(let y=-.03;y<.03;y+=.0001){const v=sunWaterVisibility(y,.02);assert(v>=prior&&v-prior<.004);prior=v;}
});
test('wheel translates both camera and target without changing FOV or orbit distance',()=>{
 const events={},camera=new T.PerspectiveCamera(57);camera.position.set(0,2,10);
 const controls={object:camera,target:new T.Vector3(0,2,0),enabled:true,update(){},dispatchEvent(){}};
 const el={clientHeight:720,addEventListener(k,v){events[k]=v;},removeEventListener(k){delete events[k];}};
 const input=configureCameraInput(controls,el);events.wheel({deltaY:-100,deltaMode:0,preventDefault(){},stopImmediatePropagation(){}});
 assert.equal(camera.fov,57);assert.equal(camera.position.z,8.8);assert(Math.abs(camera.position.distanceTo(controls.target)-10)<1e-8);input.dispose();assert.equal(events.wheel,undefined);
});

import {readFile} from 'node:fs/promises';
test('clock stays in the icon row and all display controls have one accessible input',async()=>{
 const html=await readFile(new URL('./index.html',import.meta.url),'utf8');
 assert.match(html,/<header[\s\S]*id="timeButton"[\s\S]*<\/header>/);
 assert(!html.includes('观看参考视频'));
 for(const id of ['windWaves','waveStrength','waterReflection','sunReflection','geometryDetail','boardClarity'])assert.equal(html.split('id="'+id+'"').length-1,1);
});
