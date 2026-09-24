export const WEATHER_URL='https://api.open-meteo.com/v1/forecast?latitude=31.2304&longitude=121.4737&current=temperature_2m,relative_humidity_2m,precipitation,weather_code,cloud_cover,wind_speed_10m,wind_direction_10m&daily=sunrise,sunset&timezone=Asia%2FShanghai&forecast_days=1';
const labels=code=>code===0?'晴':code===1?'晴间多云':code===2?'多云':code===3?'阴':code===45||code===48?'雾':code>=95?'雷雨':code>=71&&code<=77||code===85||code===86?'雪':code>=51?'雨':'天气未知';
export function parseWeather(data,now=Date.now()){
 const c=data?.current;if(!c||!Number.isFinite(c.cloud_cover)||!Number.isFinite(c.temperature_2m)||!Number.isFinite(c.weather_code))throw Error('天气数据不完整');
 return {fetched:now,time:c.time,code:c.weather_code,label:labels(c.weather_code),temperature:c.temperature_2m,cloud:Math.max(0,Math.min(1,c.cloud_cover/100)),rain:Math.max(0,c.precipitation||0),fog:c.weather_code===45||c.weather_code===48?1:0,wind:Math.max(0,c.wind_speed_10m||0),windDirection:Number.isFinite(c.wind_direction_10m)?((c.wind_direction_10m%360)+360)%360:null,sunrise:data.daily?.sunrise?.[0]?.slice(11,16)||'',sunset:data.daily?.sunset?.[0]?.slice(11,16)||''};
}
export function createShanghaiWeather({onChange,fetcher=fetch,storage=globalThis.localStorage,now=Date.now}={}){
 let value=null,timer=null,stopped=false,controller=null;const key='refuge-shanghai-weather-v2';
 try{const c=JSON.parse(storage.getItem(key));if(c&&Number.isFinite(c.fetched)&&Number.isFinite(c.cloud)&&Number.isFinite(c.temperature)&&now()-c.fetched<7200000&&now()>=c.fetched)value=c;}catch{}
 async function refresh(){
  controller=new AbortController();const timeout=setTimeout(()=>controller.abort(),10000);
  try{const response=await fetcher(WEATHER_URL,{signal:controller.signal});if(!response.ok)throw Error('天气服务暂不可用');value=parseWeather(await response.json(),now());try{storage.setItem(key,JSON.stringify(value));}catch{}if(!stopped)onChange?.(value,'live');}
  catch{if(value&&now()-value.fetched>=7200000)value=null;if(!stopped)onChange?.(value,value?'cached':'unavailable');}
  finally{clearTimeout(timeout);if(!stopped)timer=setTimeout(refresh,900000);}
 }
 if(value)onChange?.(value,'cached');if(!value||now()-value.fetched>=900000)refresh();else timer=setTimeout(refresh,900000-(now()-value.fetched));
 return {dispose(){stopped=true;clearTimeout(timer);controller?.abort();},refresh};
}
