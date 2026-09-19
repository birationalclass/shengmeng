// All viewpoints share the peninsula plan: east +X, north -Z.
import {BUILDING_SCALE} from './site-layout.js?v=10-offshore';
export const SHOTS=[
  {name:'海岸抵达',title:'海上相连，<br>一处安心思考的地方。',description:'海上模块平台 · 水院别墅 · 可扩展园区',duration:28,fov:49,
   positions:[[85,22,45],[74,17,36],[64,12,29],[55,8,24]],targets:[[10,2,0],[12,2,0],[14,2,0],[18,2,0]]},
  {name:'水庭',title:'跨过一座小桥，<br>让思绪沿水面展开。',description:'环绕泳池 · 露天内核水院 · 小拱桥',duration:22,fov:52,
   positions:[[-26,1.8,8],[-23,1.7,8],[-18,1.6,8],[-13,1.7,8]],targets:[[3.5,.4,9],[3.5,.4,9],[3.5,.4,7],[3.5,.4,2]]},
  {name:'书室',title:'把安静，<br>留给还未完成的想法。',description:'独立图书馆 · 书架与研究桌 · 林间阅读',duration:26,fov:59,
   positions:[[-37,1.6,-9],[-37,1.5,-12],[-37,1.5,-16],[-37,1.5,-18]],targets:[[-37,1.4,-20],[-38,1.5,-20],[-39,1.5,-20],[-38,1.5,-20]]},
  {name:'报告厅',title:'面朝大海，<br>围绕黑板展开讨论。',description:'低矮紧凑 · 三十二席科技座椅 · 朝东讲台',duration:30,fov:61,
   positions:[[35.3,1.2,0],[36.5,1.2,0],[38.4,1.2,0],[40.2,1.2,0]],targets:[[42.7,1.3,0],[42.7,1.3,0],[42.7,1.3,0],[42.7,1.3,0]]},
  {name:'板书',title:'一页一页，<br>让推理留下痕迹。',description:'六块升降黑板 · 粉笔落粉 · 擦除后续写',duration:70,fov:57,lecture:true,
   positions:[[39,1.4,-2.4],[39,1.4,-1],[39,1.4,1],[39,1.4,2.4]],targets:[[42.7,1.4,-2.4],[42.7,1.4,-1],[42.7,1.4,1],[42.7,1.4,2.4]]},
  {name:'海景露台',title:'从无边池沿，<br>望向日出与海平线。',description:'正东无边泳池 · 独立回水槽 · 无遮挡海景',duration:30,fov:58,
   positions:[[47,1.5,5],[48,1.5,2],[51,1.5,0],[52,1.5,-2]],targets:[[150,0,4.5],[150,0,2],[150,0,-2],[150,0,-4.5]]},
  {name:'远眺',title:'把空间留白，<br>也把未来留给下一座小屋。',description:'北东南环海 · 海上栈桥与扩建 · 分散小别墅',duration:28,fov:50,
   positions:[[-28,18,40],[-35,25,49],[-43,32,58],[-52,38,67]],targets:[[9,1,0],[10,1,0],[12,1,0],[14,1,0]]},
  {name:'山水花园',title:'竹影、溪声，<br>与一棵巨树为邻。',description:'海上花园 · 竹庭茶亭 · 西岸山水远景',duration:38,fov:58,
   positions:[[-23,3,36],[-37,5,30],[-58,6,12],[-68,8,-20]],targets:[[-24,4,31],[-44,4,30],[-51,6,8],[-194,12,-36]]}
];
for(const shot of SHOTS)for(const key of ['positions','targets'])shot[key]=shot[key].map(p=>p.map(v=>v*BUILDING_SCALE));
export function smoothProgress(t){return t*t*(3-2*t);}
export function fadeAt(t){return Math.max(0,1-t/.035,(t-.965)/.035);}
export function advanceShot(index,time,delta,speed){
  time+=Math.min(.1,Math.max(0,delta))*speed;
  while(time>=SHOTS[index].duration){time-=SHOTS[index].duration;index=(index+1)%SHOTS.length;}
  return {index,time};
}
