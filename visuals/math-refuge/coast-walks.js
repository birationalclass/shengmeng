import {fromBeach,COAST_LIFT,branchCentre} from './elliptic-site.js?v=true-north-coast-1';
import {ringPoint} from '../ocean/elliptic-model.js';

export const WALK_MENU={name:'漫步',walk:true,rooms:[
 {name:'海岸总览',shot:'曲线海岸总览'},
 {name:'左环漫滩',shot:'左环漫滩'},
 {name:'右上沙滩',shot:'右上沙滩'},
 {name:'右下沙滩',shot:'右下沙滩'}
]};
const world=([x,y,z])=>{const [wx,wz]=fromBeach(x,z);return [wx,y+COAST_LIFT,wz];};
function route(name,points,speed,description){
 const positions=points.map(world),targets=points.map((p,i)=>{
  const a=points[Math.max(0,i-1)],b=points[Math.min(points.length-1,i+1)];
  const length=Math.hypot(b[0]-a[0],b[2]-a[2])||1;
  return world([p[0]+(b[0]-a[0])/length*65,p[1]-8,p[2]+(b[2]-a[2])/length*65]);
 });
 const length=positions.slice(1).reduce((sum,p,i)=>sum+Math.hypot(...p.map((v,k)=>v-positions[i][k])),0);
 return {name,title:name,description,walk:true,duration:length/speed+3,fov:60,positions,targets};
}
export function installCoastWalks(shots){
 const ring=Array.from({length:161},(_,i)=>{const [x,z]=ringPoint(i/160*Math.PI*2);return [x,12,z];});
 const routes=[route('左环漫滩',ring,6,'沿左环沙滩环行 · 可随时手动接管')];
 for(const [name,end] of [['右上沙滩',-1800],['右下沙滩',1800]]){
  const points=Array.from({length:121},(_,i)=>{
   const t=i/120,z=80+(end-80)*t;
   // Both routes begin at the existing main-hall beach viewpoint (2040,16,80).
   const correction=(2040-branchCentre(80)-40)*Math.exp(-t*20);
   return [branchCentre(z)+40+correction,16,z];
  });
  routes.push(route(name,points,6,'主楼沙滩出发 · 沿右滩向'+(end<0?'北':'南')+'漫步 · 可随时手动接管'));
 }
 const overview=Array.from({length:121},(_,i)=>{const z=1600-i/120*3200;return [branchCentre(z)+400,460,z];});
 const full=route('曲线海岸总览',overview,30,'沿右侧海岸缓行俯瞰 · 左环与建筑群尽收眼底');
 full.fov=72;full.targets=overview.map(p=>world([p[0]-650,3,p[2]]));routes.push(full);
 for(const r of routes){const i=shots.findIndex(s=>s.name===r.name);if(i<0)shots.push(r);else shots[i]=r;}
}
// Three-second velocity ramps; constant travel speed through the middle.
export function walkProgress(time,duration){
 const t=Math.max(0,Math.min(duration,time)),r=Math.min(3,duration/3);
 const start=x=>{const u=x/r;return r*(u*u*u-.5*u*u*u*u);};
 return t<r?start(t)/(duration-r):t>duration-r?1-start(duration-t)/(duration-r):(t-r/2)/(duration-r);
}
