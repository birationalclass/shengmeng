// NOAA fractional-year approximation; fixed Shanghai coordinates, UTC+8.
// https://gml.noaa.gov/grad/solcalc/solareqns.PDF
export const smooth=(a,b,x)=>{const t=Math.max(0,Math.min(1,(x-a)/(b-a)));return t*t*(3-2*t);};
export const shanghaiHour=(date=new Date())=>{const d=new Date(+date+8*3600000);return d.getUTCHours()+d.getUTCMinutes()/60+d.getUTCSeconds()/3600+d.getUTCMilliseconds()/3600000;};
export function solarState(hour,date=new Date()){
 const local=new Date(+date+8*3600000),year=local.getUTCFullYear(),start=Date.UTC(year,0,1),n=Math.floor((Date.UTC(year,local.getUTCMonth(),local.getUTCDate())-start)/86400000)+1,days=(Date.UTC(year+1,0,1)-start)/86400000;
 const h=((hour%24)+24)%24,g=2*Math.PI/days*(n-1+(h-12)/24),eq=229.18*(.000075+.001868*Math.cos(g)-.032077*Math.sin(g)-.014615*Math.cos(2*g)-.040849*Math.sin(2*g));
 const dec=.006918-.399912*Math.cos(g)+.070257*Math.sin(g)-.006758*Math.cos(2*g)+.000907*Math.sin(2*g)-.002697*Math.cos(3*g)+.00148*Math.sin(3*g),lat=31.2304*Math.PI/180,H=(h*60+eq+4*121.4737-480-720)*Math.PI/720;
 const east=-Math.cos(dec)*Math.sin(H),up=Math.sin(lat)*Math.sin(dec)+Math.cos(lat)*Math.cos(dec)*Math.cos(H),south=Math.sin(lat)*Math.cos(dec)*Math.cos(H)-Math.cos(lat)*Math.sin(dec),elevation=Math.asin(Math.max(-1,Math.min(1,up)))*180/Math.PI;
 const daylight=smooth(-6,12,elevation),direct=smooth(-.8,3,elevation),warm=1-smooth(0,20,elevation);
 return {direction:[east,up,south],elevation,daylight,direct,warm,night:1-smooth(-9,-2,elevation),physicalRadius:.00465*(1+.0167*Math.cos(g)),radius:.00465*(1+.0167*Math.cos(g)),solarNoon:(720-4*121.4737-eq+480)/60};
}
export function approachHour(current,target,dt){const delta=(((target-current+12)%24+24)%24)-12;return current+delta*(1-Math.exp(-Math.max(0,dt)/.55));}

// Sunrise/sunset fallback at the conventional -0.833 degree centre elevation.
export function solarEvents(date=new Date()){
 const crossing=(lo,hi,rising)=>{for(let i=0;i<30;i++){const mid=(lo+hi)/2,above=solarState(mid,date).elevation>-.833;if(above===rising)hi=mid;else lo=mid;}return(lo+hi)/2;};
 return {sunrise:crossing(0,12,true),sunset:crossing(12,24,false)};
}
