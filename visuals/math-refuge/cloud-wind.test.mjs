import test from 'node:test';import assert from 'node:assert/strict';
import {windVelocity,advanceCloudWind,cloudTimeRate,advanceWeatherWinds} from './cloud-wind.js';
import {parseWeather,WEATHER_URL} from './shanghai-weather.js';
test('weather requests wind direction and distinguishes missing data from north wind',()=>{
 assert(WEATHER_URL.includes('wind_direction_10m'));
 const current={temperature_2m:20,cloud_cover:70,weather_code:2,wind_speed_10m:36};
 assert.equal(parseWeather({current}).windDirection,null);
 assert.equal(parseWeather({current:{...current,wind_direction_10m:360}}).windDirection,0);
});
test('meteorological from bearings map correctly to scene axes and km/s',()=>{
 assert(Math.abs(windVelocity(36,0).z-.01)<1e-10);
 assert(Math.abs(windVelocity(36,90).x+.01)<1e-10);
 assert(Math.abs(windVelocity(36,180).z+.01)<1e-10);
 assert(Math.abs(windVelocity(36,270).x-.01)<1e-10);
 assert.equal(Math.hypot(...Object.values(windVelocity(0,270))),0);
});
test('wind changes preserve position and interpolate across north without a full rotation',()=>{
 const state={velocity:windVelocity(36,359),offset:{x:3,z:4}};
 advanceCloudWind(state,36,1,0);assert.deepEqual(state.offset,{x:3,z:4});
 advanceCloudWind(state,36,1,1);assert(state.velocity.z>.0099);assert(Math.abs(state.offset.x-3)<.001);assert(Math.abs(state.offset.z-4.01)<.00001);
 const calm={velocity:windVelocity(0,0),offset:{x:0,z:0}};advanceCloudWind(calm,0,90,1);assert.deepEqual(calm.offset,{x:0,z:0});
});

test('time acceleration saturates smoothly at two while preserving wind and water speed',()=>{
 assert.equal(cloudTimeRate(1),1);let previous=0;for(const rate of [0,1,2,10,60,600,1e6]){const v=cloudTimeRate(rate);assert(v>=previous&&v<=2);previous=v;}
 const state=speed=>({velocity:windVelocity(speed,270),offset:{x:0,z:0}});
 const a=state(36),b=state(72),water=state(36);advanceWeatherWinds(a,water,36,270,.1,600);advanceWeatherWinds(b,state(72),72,270,.1,600);
 assert(Math.abs(b.offset.x-2*a.offset.x)<1e-10);assert(Math.abs(a.offset.x-.002)<1e-10);assert(Math.abs(water.offset.x-.001)<1e-10);
});

test('one minute at 60x or 6000x never advects beyond twice real wind distance',()=>{
 for(const rate of [1,5,60,6000]){const cloud={velocity:windVelocity(36,270),offset:{x:0,z:0}},water={velocity:windVelocity(36,270),offset:{x:0,z:0}};
 for(let frame=0;frame<3600;frame++)advanceWeatherWinds(cloud,water,36,270,1/60,rate);
 assert(Math.hypot(cloud.offset.x,cloud.offset.z)<=1.2+1e-9);assert(Math.abs(water.offset.x-.6)<1e-9);
 assert(Math.abs(cloud.offset.x-.6*cloudTimeRate(rate))<1e-9);
 }
});
