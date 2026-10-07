import test from 'node:test';import assert from 'node:assert/strict';import {bindPhysicalButtons,physicalHitAction} from './physical-buttons.js';
class Canvas extends EventTarget {style={cursor:''};setPointerCapture(){}releasePointerCapture(){}}
function event(type,x=10,y=10){const e=new Event(type,{cancelable:true});Object.assign(e,{button:0,pointerId:1,clientX:x,clientY:y,buttons:type==='pointerdown'?1:0});return e;}
test('smart-glass short taps activate once and pulse; drags and cancellation never activate',()=>{
 const canvas=new Canvas(),controls={enabled:true},object={userData:{action:'voice:toggle',smartGlass:true}},actions=[],binding=bindPhysicalButtons(canvas,controls,()=>object,a=>actions.push(a));
 canvas.dispatchEvent(event('pointermove'));assert(object.userData.hovered);assert.equal(canvas.style.cursor,'pointer');canvas.dispatchEvent(event('pointerdown'));assert(object.userData.pressed);assert.equal(controls.enabled,false);canvas.dispatchEvent(event('pointerup'));assert.equal(actions.length,1);assert.equal(object.userData.clickPulse,1);assert.equal(controls.enabled,true);assert.equal(object.userData.pressed,false);
 object.userData.clickPulse=0;canvas.dispatchEvent(event('pointerdown'));canvas.dispatchEvent(event('pointerup',35,10));assert.equal(actions.length,1);assert.equal(object.userData.clickPulse,0);canvas.dispatchEvent(event('pointerdown'));canvas.dispatchEvent(event('pointercancel'));assert.equal(controls.enabled,true);canvas.dispatchEvent(event('pointerup'));assert.equal(actions.length,1);binding.dispose();assert.equal(object.userData.hovered,false);
});
test('loading progress icons have no action and cannot consume a camera press',()=>{
 const canvas=new Canvas(),controls={enabled:true};let count=0;const binding=bindPhysicalButtons(canvas,controls,()=>({userData:{action:null,smartGlass:true}}),()=>count++);canvas.dispatchEvent(event('pointerdown'));assert(controls.enabled);canvas.dispatchEvent(event('pointerup'));assert.equal(count,0);binding.dispose();
});

test('audio byte progress cannot turn a play button into the lectern page scrubber',()=>{
 for(const progress of [null,0,.6,1])assert.equal(physicalHitAction({object:{userData:{action:'voice:toggle',progress}},uv:{x:.7}},{startAt:0,stopAt:29}),'voice:toggle');
 assert.equal(physicalHitAction({object:{userData:{action:'page:seek:0',progress:true}},uv:{x:.5}},{startAt:3,stopAt:13}),'page:seek:8');
 assert.equal(physicalHitAction({object:{userData:{action:null,loadProgress:.5}},uv:{x:.5}}),null);
});
