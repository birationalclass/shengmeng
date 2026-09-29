import test from 'node:test';
import assert from 'node:assert/strict';
import {AdaptiveQuality,RenderClock,renderRatio,QUALITY} from './render-quality.mjs';
function run(q,seconds,dt){for(let t=0;t<seconds;t+=dt)q.sample(dt);}
test('mobile uses the same initial budget in either orientation; pixel budget bounds large canvases',()=>{assert.equal(new AdaptiveQuality({mobile:true}).current.id,'balanced');for(const [w,h] of [[390,844],[844,390],[3840,2160]])for(const q of QUALITY){const r=renderRatio(w,h,3,q);assert.ok(w*h*r*r<=q.pixels+1);assert.ok(r<=q.dpr);}});
test('sustained slowness lowers auto quality but isolated loading stalls do not',()=>{const q=new AdaptiveQuality();run(q,4,1/60);q.sample(.8);assert.equal(q.level,2);run(q,8,1/30);assert.equal(q.level,1);run(q,10,1/30);assert.equal(q.level,0);});
test('recovery requires long stable headroom and manual choice stays fixed',()=>{const q=new AdaptiveQuality({mobile:true});run(q,20,1/60);assert.equal(q.level,1);run(q,20,1/60);assert.equal(q.level,2);q.setMode('high');run(q,30,1/15);assert.equal(q.level,2);q.setMode('power');assert.equal(q.current.fps,30);q.setMode('invalid');assert.equal(q.mode,'power');});
test('30 and 60 fps caps preserve elapsed game time on 60/120 Hz displays',()=>{for(const hz of [60,120])for(const fps of [30,60]){const clock=new RenderClock();let elapsed=0,frames=0;for(let i=0;i<hz*10;i++){const dt=clock.advance(1/hz,fps);if(dt){elapsed+=dt;frames++;}}assert.ok(Math.abs(elapsed-10)<1/fps+.001);assert.ok(Math.abs(frames-fps*10)<=1,`${hz}/${fps}: ${frames}`);}});
test('pause clears accumulated time instead of advancing on resume',()=>{const clock=new RenderClock();clock.advance(.01,30);clock.advance(.01,30);clock.reset();assert.equal(clock.advance(.016,30),.016);});

test('persistently very slow devices still downshift instead of treating every frame as loading',()=>{const q=new AdaptiveQuality();run(q,20,.3);assert.equal(q.level,0);});
