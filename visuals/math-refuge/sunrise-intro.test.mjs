import test from 'node:test';
import assert from 'node:assert/strict';
import {RetreatTime} from './retreat-time.js';
import {TimePresentation} from './time-presentation.js';
import {SunriseIntro} from './sunrise-intro.js';
test('opening starts before sunrise at 30x then restores actual time under a fade',()=>{
 const clock=new RetreatTime(()=>new Date('2026-09-25T12:00:00Z'),()=>20),view=new TimePresentation(20),intro=new SunriseIntro(clock,view);
 intro.start(6);assert.equal(clock.rate,30);assert.ok(Math.abs(clock.hour-5.975)<1e-8);
 for(let i=0;i<299;i++){intro.update(.1);clock.update(.1);}assert.equal(clock.preview,true);
 intro.update(.11);assert.equal(clock.preview,false);assert.equal(clock.hour,20);assert.equal(view.phase,'out');
});
test('manual time choice cancels the automatic return',()=>{
 const clock=new RetreatTime(),view=new TimePresentation(12),intro=new SunriseIntro(clock,view);
 intro.start(6);intro.cancel();clock.previewAt(23);intro.update(60);assert.equal(clock.hour,23);assert.equal(clock.preview,true);
});
