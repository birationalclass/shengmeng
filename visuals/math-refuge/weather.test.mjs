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
 let min=Infinity,max=0;for(let x=-350;x<=350;x+=4)for(let z=-350;z<=350;z+=4){const d=seaDepthAt(x,z);min=Math.min(min,d);max=Math.max(max,d);assert(Math.abs(seaDepthAt(x+.01,z)-d)<.015);assert(Math.abs(seaDepthAt(x,z+.01)-d)<.015);}
 assert(min>1&&max<110);assert(seaDepthAt(400,0)>seaDepthAt(-78,16)+40);assert(seaDepthAt(28,0)>seaDepthAt(-78,16));
});
test('weather readings validate data, keep cloud cover bounded and expose source time',()=>{
 const w=parseWeather({current:{temperature_2m:26,cloud_cover:20,weather_code:1,time:'2026-09-24T12:00',precipitation:0,wind_speed_10m:9},daily:{sunrise:['2026-09-24T05:43'],sunset:['2026-09-24T17:48']}},5);assert.equal(w.cloud,.2);assert.equal(w.label,'晴间多云');assert.equal(w.sunrise,'05:43');assert.equal(w.fetched,5);assert.throws(()=>parseWeather({current:{temperature_2m:25}}));
});
test('weather network failure is labelled unavailable instead of claiming a real clear sky',async()=>{
 const events=[];let resolve;const ready=new Promise(r=>resolve=r);const service=createShanghaiWeather({storage:{getItem(){return null;}},fetcher:async()=>{throw Error('offline');},onChange:(value,status)=>{events.push([value,status]);resolve();}});await ready;service.dispose();assert.deepEqual(events,[[null,'unavailable']]);
});

test('stars fade through twilight and sunrise is tripled and ordinary sun doubled',()=>{const date=new Date('2026-09-24T04:00:00Z');const noon=solarState(12,date),night=solarState(0,date);assert.equal(noon.night,0);assert.equal(night.night,1);let horizon;for(let h=5;h<7;h+=.001){const s=solarState(h,date);if(!horizon||Math.abs(s.elevation)<Math.abs(horizon.elevation))horizon=s;}assert(horizon.radius/noon.radius>1.5);assert(Math.abs(horizon.radius/horizon.physicalRadius-4.95)<.001);assert(noon.radius/noon.physicalRadius===2);const sunset=solarState(solarEvents(date).sunset,date);const oldScale=1+.65*(1-((x)=>x*x*(3-2*x))(Math.abs(sunset.elevation)/14));assert(Math.abs(sunset.radius/sunset.physicalRadius-2*oldScale)<1e-10);});
import {RetreatTime} from './retreat-time.js';import {solarEvents} from './solar-state.js';
test('accelerated clock supports play, pause, 60x cap, midnight wrapping and resync',()=>{const clock=new RetreatTime(()=>new Date('2026-09-24T04:00:00Z'),shanghaiHour);assert.equal(clock.hour,12);clock.previewAt(23.99);clock.play(100);assert.equal(clock.rate,60);clock.update(60);assert(Math.abs(clock.hour-.99)<1e-10);clock.pause();const hour=clock.hour;clock.update(60);assert.equal(clock.hour,hour);clock.setRate(5);clock.play();clock.update(720);assert(Math.abs(clock.hour-(hour+1))<1e-10);clock.sync();assert.equal(clock.hour,12);assert.equal(clock.playing,false);assert.equal(clock.preview,false);});
test('sunrise and sunset fallback bracket the Shanghai horizon',()=>{const date=new Date('2026-09-24T04:00:00Z'),events=solarEvents(date);assert(events.sunrise>5&&events.sunrise<7);assert(events.sunset>17&&events.sunset<19);for(const h of Object.values(events))assert(Math.abs(solarState(h,date).elevation+.833)<.00001);assert(solarState(events.sunrise-.05,date).elevation<-.833);assert(solarState(events.sunset+.05,date).elevation<-.833);});
