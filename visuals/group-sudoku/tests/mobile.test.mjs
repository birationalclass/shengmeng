import test from 'node:test';import assert from 'node:assert/strict';
import * as T from '../../3d/vendor/three.module.js';
import {mobileDevice,mobileFrameRate,gentleZoom,mobileFrameScale,bindPinch} from '../mobile.mjs';
import {SudokuAtlas,PLACES} from '../atlas.mjs';
test('mobile power policy caps interactive and idle frames, and pinch cannot jump',()=>{
 assert(mobileDevice(390,844));assert(mobileDevice(844,390));assert(!mobileDevice(1440,900));assert.equal(mobileFrameRate(),15);assert.equal(mobileFrameRate({moving:true}),30);
 assert(Math.abs(gentleZoom(60,1.02,60)-60)<.4);assert(gentleZoom(60,100,60)>55);
 let r=60;for(let i=0;i<100;i++)r=gentleZoom(r,2,60);assert.equal(r,51);for(let i=0;i<100;i++)r=gentleZoom(r,.5,60);assert.equal(r,78);
});
test('portrait and short landscape frame the complete disk away from screen edges',()=>{
 for(const [w,h]of [[390,844],[844,390],[667,375],[932,430]]){
 const camera=new T.PerspectiveCamera(40,w/h,.65,900),fake={mobile:true,canvas:{clientWidth:w,clientHeight:h},camera};
 camera.setViewOffset(w,h,0,-h*.04,w,h);camera.updateProjectionMatrix();
 const {pos,aim}=SudokuAtlas.prototype.playPose.call(fake,0);camera.position.copy(pos);camera.lookAt(aim);camera.updateMatrixWorld(true);
 for(let i=0;i<64;i++){const q=i*Math.PI/32,p=new T.Vector3(PLACES[0][0]+Math.sin(q)*13.1,0,PLACES[0][1]+Math.cos(q)*13.1).project(camera);assert(Math.abs(p.x)<.95,`${w}x${h} horizontal ${p.x}`);assert(Math.abs(p.y)<.82,`${w}x${h} vertical ${p.y}`);}
 assert(mobileFrameScale(w,h)>=1.18);
 }
});
test('pinch suppresses accidental board taps and releases state on cancellation',()=>{
 const element=new EventTarget(),zooms=[];let starts=0,ends=0;const pinch=bindPinch(element,{enabled:()=>true,zoom:r=>zooms.push(r),onStart:()=>starts++,onEnd:()=>ends++});
 const emit=(name,touches)=>{const e=new Event(name,{cancelable:true});e.touches=touches.map(([clientX,clientY])=>({clientX,clientY}));element.dispatchEvent(e);return e;};
 emit('touchstart',[[0,0],[100,0]]);assert(pinch.active);emit('touchmove',[[0,0],[110,0]]);assert.deepEqual(zooms,[1.1]);emit('touchcancel',[]);assert(!pinch.active);assert.equal(starts,1);assert.equal(ends,1);assert(emit('click',[]).defaultPrevented);
});
