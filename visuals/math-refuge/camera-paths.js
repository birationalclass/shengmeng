// Original architectural shots, with dedicated seminar and ocean chapters.
import {BUILDING_SCALE} from './site-layout.js?v=7-garden';
export const SHOTS=[
  {name:'海岸抵达',title:'山海之间，<br>留一处思考的地方。',description:'错层书院 · 连桥会议翼 · 临海露台',duration:28,fov:49,
   positions:[[72,34,61],[65,28,52],[56,23,43],[49,18,35]],targets:[[13,4,-1],[14,4,-1],[16,4,-1],[19,3,-1]]},
  {name:'水庭',title:'让思绪，<br>沿着水面展开。',description:'低位推进 · 水面反射 · 悬浮石阶',duration:22,fov:52,
   positions:[[12,2.25,15],[10,2.2,12],[7.4,2.2,9],[5.2,2.2,5.3]],targets:[[0,3,0],[-2,3,-2],[-3,3,-4],[-3,3,-6]]},
  {name:'书室',title:'没有结论的时候，<br>也可以先坐一会儿。',description:'沿窗漫游 · 书架与黑板 · 开放讨论区',duration:26,fov:59,
   positions:[[-8,2.3,2],[-8,2.3,-1],[-6.5,2.3,-4],[-3,2.3,-5]],targets:[[0,2.5,-6],[1,2.5,-7],[3,2.6,-6],[5,2.6,-5]]},
  {name:'报告厅',title:'面向黑板，<br>让思想在这里相遇。',description:'三十二席分排座椅 · 中央通道 · 小讲台',duration:30,fov:61,
   positions:[[28,2.6,7],[28,2.5,3],[28,2.5,-1],[28,2.5,-5]],targets:[[28,2.4,-9],[28,2.4,-10],[28,2.6,-10.4],[28,2.6,-10.4]]},
  {name:'板书',title:'一页一页，<br>让推理留下痕迹。',description:'粉笔书写 · 三组上下交替 · 擦除后续写',duration:70,fov:57,lecture:true,
   positions:[[22.4,2.7,-4],[23,2.7,-4],[28,2.7,-4],[33.6,2.7,-4]],targets:[[22.4,2.7,-10.5],[23,2.7,-10.5],[28,2.7,-10.5],[33.6,2.7,-10.5]]},
  {name:'海景露台',title:'把难题留在纸上，<br>把目光交给大海。',description:'开阔海平线 · 动态波光 · 临海阅读席',duration:30,fov:58,
   positions:[[40,2.4,9],[42,2.4,5],[44,2.4,0],[45,2.4,-5]],targets:[[125,-2,-10],[130,-2,-12],[140,-2,-14],[150,-2,-17]]},
  {name:'远眺',title:'这里不急着，<br>给每个问题一个答案。',description:'升空退远 · 双翼书院 · 山海全景',duration:28,fov:50,
   positions:[[-25,21,42],[-31,26,50],[-38,31,57],[-48,37,66]],targets:[[21,3,-1],[24,3,-1],[28,2,-1],[33,1,-1]]},
  {name:'山水花园',title:'竹影、溪声，<br>与一棵巨树为邻。',description:'草坪花境 · 竹林溪径 · 山间瀑布',duration:38,fov:58,
   positions:[[-10,5.5,24],[-22,6.5,16],[-24,8,-10],[-25,10,-31]],targets:[[-22,3,13],[-32,5,-12],[-33,9,-40],[-35,14,-46]]}
];
for(const shot of SHOTS)for(const key of ['positions','targets'])shot[key]=shot[key].map(p=>p.map(v=>v*BUILDING_SCALE));
export function smoothProgress(t){return t*t*(3-2*t);}
export function fadeAt(t){return Math.max(0,1-t/.035,(t-.965)/.035);}
export function advanceShot(index,time,delta,speed){
  time+=Math.min(.1,Math.max(0,delta))*speed;
  while(time>=SHOTS[index].duration){time-=SHOTS[index].duration;index=(index+1)%SHOTS.length;}
  return {index,time};
}
