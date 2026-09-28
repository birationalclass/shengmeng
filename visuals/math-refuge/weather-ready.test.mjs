import assert from 'node:assert/strict';
import {createShanghaiWeather} from './shanghai-weather.js';
const storage={getItem:()=>null,setItem(){}};
for(const fails of [false,true]){
 let state='loading';const service=createShanghaiWeather({storage,fetcher:async()=>{if(fails)throw Error('offline');return {ok:true,json:async()=>({current:{cloud_cover:70,temperature_2m:20,weather_code:2}})};},onChange:(_,s)=>state=s});
 assert(service.ready instanceof Promise);await service.ready;assert.equal(state,fails?'unavailable':'live');service.dispose();
}
console.log('PASS weather readiness resolves after success or explicit fallback');
