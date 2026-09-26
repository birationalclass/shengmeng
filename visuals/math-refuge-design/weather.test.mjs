import test from 'node:test';import assert from 'node:assert/strict';
import {solarState,approachHour,shanghaiHour} from './solar-state.js';
import {seaDepthAt} from './sea-depth.js';import {parseWeather,createShanghaiWeather} from './shanghai-weather.js';
test('Shanghai solar motion and twilight are continuous across sunrise, sunset and midnight',()=>{
 const d=new Date('2026-09-24T04:00:00Z');let prior=solarState(0,d);
 for(let h=1/3600;h<=24;h+=1/3600){const s=solarState(h,d);assert(s.direction.every(Number.isFinite));assert(Math.abs(Math.hypot(...s.direction)-1)<1e-10);assert(s.daylight>=0&&s.daylight<=1);assert(Math.hypot(...s.direction.map((v,i)=>v-prior.direction[i]))<.001);assert(Math.abs(s.daylight-prior.daylight)<.001);assert(Math.abs(s.direct-prior.direct)<.003);assert(Math.abs(s.night-prior.night)<.003);assert(Math.abs(s.radius-prior.radius)<.00002);prior=s;}
 const morning=solarState(7,d),evening=solarState(17,d);assert(morning.direction[0]>0&&evening.direction[0]<0);assert(solarState(12,d).elevation>50);assert(solarState(0,d).daylight===0);assert.equal(shanghaiHour(new Date('2026-09-24T00:00:00Z')),8);
 assert(approachHour(23.99,.01,.1)>23.99);assert(approachHour(.01,23.99,.1)<.01);
});
test('bathymetry is bounded, smooth and deepens into open water',()=>{
 let min=Infinity,max=0;for(let x=-350;x<=350;x+=4)for(let z=-350;z<=350;z+=4){const d=seaDepthAt(x,z);min=Math.min(min,d);max=Math.max(max,d);assert(Math.abs(seaDepthAt(x+.01,z)-d)<.06);assert(Math.abs(seaDepthAt(x,z+.01)-d)<.06);}
 assert(min>-1&&max<110);assert(seaDepthAt(400,0)>seaDepthAt(-78,16)+40);assert(seaDepthAt(28,0)<3);
});
test('weather readings validate data, keep cloud cover bounded and expose source time',()=>{
 const w=parseWeather({current:{temperature_2m:26,cloud_cover:20,weather_code:1,time:'2026-09-24T12:00',precipitation:0,wind_speed_10m:9},daily:{sunrise:['2026-09-24T05:43'],sunset:['2026-09-24T17:48']}},5);assert.equal(w.cloud,.2);assert.equal(w.label,'晴间多云');assert.equal(w.sunrise,'05:43');assert.equal(w.fetched,5);assert.throws(()=>parseWeather({current:{temperature_2m:25}}));
});
test('weather network failure is labelled unavailable instead of claiming a real clear sky',async()=>{
 const events=[];let resolve;const ready=new Promise(r=>resolve=r);const service=createShanghaiWeather({storage:{getItem(){return null;}},fetcher:async()=>{throw Error('offline');},onChange:(value,status)=>{events.push([value,status]);resolve();}});await ready;service.dispose();assert.deepEqual(events,[[null,'unavailable']]);
});

test('solar angular diameter stays physical at noon and both horizons',()=>{const d=new Date('2026-09-24T04:00:00Z');for(let h=0;h<24;h+=.1){const s=solarState(h,d);assert.equal(s.radius,s.physicalRadius);assert(s.radius>.0044&&s.radius<.0049);}assert.equal(solarState(12,d).night,0);assert.equal(solarState(0,d).night,1);});
import {RetreatTime} from './retreat-time.js';import {solarEvents} from './solar-state.js';
test('accelerated clock supports play, pause, 60x cap, midnight wrapping and resync',()=>{const clock=new RetreatTime(()=>new Date('2026-09-24T04:00:00Z'),shanghaiHour);assert.equal(clock.hour,12);clock.previewAt(23.99);clock.play(100);assert.equal(clock.rate,60);clock.update(60);assert(Math.abs(clock.hour-.99)<1e-10);clock.pause();const hour=clock.hour;clock.update(60);assert.equal(clock.hour,hour);clock.setRate(5);clock.play();clock.update(720);assert(Math.abs(clock.hour-(hour+1))<1e-10);clock.sync();assert.equal(clock.hour,12);assert.equal(clock.playing,false);assert.equal(clock.preview,false);});
test('sunrise and sunset fallback bracket the Shanghai horizon',()=>{const date=new Date('2026-09-24T04:00:00Z'),events=solarEvents(date);assert(events.sunrise>5&&events.sunrise<7);assert(events.sunset>17&&events.sunset<19);for(const h of Object.values(events))assert(Math.abs(solarState(h,date).elevation+.833)<.00001);assert(solarState(events.sunrise-.05,date).elevation<-.833);assert(solarState(events.sunset+.05,date).elevation<-.833);});

import {ROOM_PADS,SEA_TERRACE,BUILDING_SCALE} from './site-layout.js';
import {RESIDENCE} from './residence-layout.js';
test('every campus building and the remote residence have shallow surrounding water',()=>{
 for(const [a,b,c,d] of [...ROOM_PADS,SEA_TERRACE,[-95,-73,-16,16]]){
  for(const [x,z] of [[a-6,c-6],[b+6,d+6],[a-6,d+6],[b+6,c-6]])assert(seaDepthAt(x,z)<=3,`deep shore at ${x},${z}`);
 }
 for(let a=0;a<Math.PI*2;a+=.04){
  const x=(RESIDENCE.origin[0]+(RESIDENCE.halfWidth+12)*Math.cos(a))/BUILDING_SCALE;
  const z=(RESIDENCE.origin[2]+(RESIDENCE.halfDepth+12)*Math.sin(a))/BUILDING_SCALE;
  assert(seaDepthAt(x,z)<3);
  assert(Math.abs(seaDepthAt(x+.01,z)-seaDepthAt(x,z))<.015);
 }
 assert(seaDepthAt(-440,0)>80,'open channel remains deep');
});
