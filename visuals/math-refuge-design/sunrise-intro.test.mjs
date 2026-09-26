import test from 'node:test';
import assert from 'node:assert/strict';
import {RetreatTime} from './retreat-time.js';
import {TimePresentation} from './time-presentation.js';
import {SunriseIntro} from './sunrise-intro.js';
test('opening accelerates continuously to real time and finishes at 1x without a fade',()=>{
 let now=Date.parse('2026-09-25T12:00:00Z');
 const clock=new RetreatTime(()=>new Date(now),d=>(d.getUTCHours()+8+d.getUTCMinutes()/60+d.getUTCSeconds()/3600)%24),view=new TimePresentation(20),intro=new SunriseIntro(clock,view);
 intro.start(6);assert.equal(clock.rate,1);assert.ok(Math.abs(clock.hour-5.9)<1e-8);
 for(let i=0;i<301;i++){now+=100;intro.update(.1);clock.update(.1);}assert(intro.catchingUp);assert(clock.preview);
 let peak=0,last=clock.hour,braked=false;
 for(let i=0;i<5000&&intro.catchingUp;i++){now+=100;intro.update(.1);clock.update(.1);peak=Math.max(peak,clock.rate);if(peak===1500&&clock.rate<200)braked=true;assert(Math.abs(((clock.hour-last+36)%24)-12)<=1500*.1/3600+1e-8);last=clock.hour;}
 assert.equal(peak,1500);assert(braked);assert(!clock.preview);assert.equal(clock.rate,1);assert.equal(view.phase,'idle');
});
test('manual time choice cancels the automatic return',()=>{
 const clock=new RetreatTime(),view=new TimePresentation(12),intro=new SunriseIntro(clock,view);
 intro.start(6);intro.cancel();clock.previewAt(23);intro.update(60);assert.equal(clock.hour,23);assert.equal(clock.preview,true);
});

test('camera approach advances at 1x, then dawn ramps to 30x over five seconds',()=>{
 const clock=new RetreatTime(),view=new TimePresentation(12),intro=new SunriseIntro(clock,view);
 intro.prepare(6);const dawn=clock.hour;
 for(let i=0;i<600;i++){intro.update(.1);clock.update(.1);}
 assert.ok(Math.abs(clock.hour-dawn-1/60)<1e-8);assert.equal(clock.playing,true);assert.equal(clock.rate,1);assert.equal(intro.elapsed,0);
 intro.arrive();clock.update(1);intro.update(1);assert.equal(clock.playing,true);assert.equal(intro.elapsed,1);
 intro.arrive();assert.equal(intro.elapsed,1);
 let last=clock.rate;for(let i=0;i<40;i++){intro.update(.1);assert(clock.rate>=last&&clock.rate-last<1);last=clock.rate;}assert(Math.abs(clock.rate-30)<1e-8);
 intro.cancel();intro.arrive();assert.equal(intro.active,false);
});

test('enlarged dawn disk starts entirely below the horizon in every season',async()=>{
 const {solarState,solarEvents}=await import('./solar-state.js');
 const {apparentAltitude}=await import('./solar-optics.js');
 for(const month of [0,2,5,8,11]){const date=new Date(2026,month,21),state=solarState(solarEvents(date).sunrise-.10,date);
  assert(apparentAltitude(state.elevation)+3*state.radius*180/Math.PI<-.1);
 }
});
