import {fromBeach,COAST_LIFT} from './elliptic-site.js?v=true-north-coast-1';
// All viewpoints share the peninsula plan: east +X, north -Z.
import {BUILDING_SCALE,DECK_Y,HALL} from './site-layout.js?v44-hall-clearance';
import {BUILDING_SHOTS} from './building-catalog.js?v=true-north-coast-1';
const loungeEye=DECK_Y*2+HALL.clearHeight/BUILDING_SCALE+.20+1.65/BUILDING_SCALE;
export const SHOTS=[
  {name:'海岸抵达',title:'海上相连，<br>一处安心思考的地方。',description:'海上长露台 · 远岛 · 可扩展园区',duration:28,fov:49,
   positions:[[90,25,48],[80,19,40],[70,13,33],[60,8,26]],targets:[[22,2,0],[24,2,0],[26,2,0],[28,2,0]]},
  {name:'庭院',title:'穿过开阔庭院，<br>让思绪沿海风展开。',description:'连续干式庭院 · 海上别墅 · 无泳池',duration:22,fov:52,
   positions:[[-26,1.8,8],[-23,1.7,8],[-18,1.6,8],[-13,1.7,8]],targets:[[3.5,.4,9],[3.5,.4,9],[3.5,.4,7],[3.5,.4,2]]},
  {name:'书室',title:'把安静，<br>留给还未完成的想法。',description:'独立图书馆 · 书架与研究桌 · 林间阅读',duration:26,fov:59,
   positions:[[-37,1.6,-9],[-37,1.5,-12],[-37,1.5,-16],[-37,1.5,-18]],targets:[[-37,1.4,-20],[-38,1.5,-20],[-39,1.5,-20],[-38,1.5,-20]]},
  {name:'报告厅',title:'面朝大海，<br>围绕黑板展开讨论。',description:'三排三十席 · 渐深地毯 · 抬高的大幅板书',duration:30,fov:61,
   positions:[[35.3,1.5,0],[36.5,1.5,0],[37.9,1.4,0],[39.2,1.3,0]],targets:[[42.7,1.9,0],[42.7,1.9,0],[42.7,1.9,0],[42.7,1.9,0]]},
  {name:'板书',title:'一页一页，<br>让推理留下痕迹。',description:'六块升降黑板 · 粉笔落粉 · 擦除后续写',duration:70,fov:57,lecture:true,
   positions:[[39,1.4,-2.4],[39,1.4,-1],[39,1.4,1],[39,1.4,2.4]],targets:[[42.7,1.4,-2.4],[42.7,1.4,-1],[42.7,1.4,1],[42.7,1.4,2.4]]},
  {name:'海景露台',title:'走上海景露台，<br>望见远岛与日出。',description:'深色石材海景露台 · 帆船与皮划艇 · 正东开阔海景',duration:30,fov:58,
   positions:[[46,1.5,3],[48,1.5,2],[51,1.5,0],[53,1.5,-2]],targets:[[180,0,4.5],[180,0,2],[180,0,-2],[180,0,-4.5]]},
  {name:'远眺',title:'把空间留白，<br>也把未来留给下一座小屋。',description:'四面环海 · 海上栈桥与扩建 · 分散小别墅',duration:28,fov:50,
   positions:[[-28,18,40],[-35,25,49],[-43,32,58],[-52,38,67]],targets:[[9,1,0],[10,1,0],[12,1,0],[14,1,0]]},
  {name:'海上花园',title:'竹影、溪声，<br>与一棵巨树为邻。',description:'海上花园 · 竹庭茶亭 · 开阔海平线',duration:38,fov:58,
   positions:[[-23,3,36],[-37,5,30],[-58,6,12],[-68,8,-20]],targets:[[-24,4,31],[-44,4,30],[-51,6,8],[-60,8,-44]]},
  {name:'二楼客厅',title:'在海景里，<br>让想法自然相遇。',description:'六套彩色 iMac · 三角钢琴 · 两组讨论环沙发 · 茶咖酒水吧',duration:34,fov:66,
   positions:[[37.5,loungeEye,4.9],[37.6,loungeEye,2.0],[37.6,loungeEye,-.3],[37.8,loungeEye,-3.3]],targets:[[40.5,loungeEye-.35,0],[40.6,loungeEye-.35,-1.5],[40.6,loungeEye-.35,-3.4],[39.5,loungeEye-.35,-5.8]]}
];
SHOTS.push({name:'教学楼',title:'三层小教室，<br>一次讲透一小节。',description:'西侧教学楼 · 每层两排座椅 · 章节研读',duration:35,fov:55,positions:[[-67,14,30],[-70,12,28],[-74,11,26],[-79,10,25]],targets:[[-85,5.3,8],[-85,5.3,8],[-85,5.3,8],[-85,5.3,8]]});
SHOTS.unshift(...SHOTS.splice(SHOTS.findIndex(s=>s.lecture),1));
SHOTS.push(...BUILDING_SHOTS);

// Coast viewpoints use the exact kilometre-to-metre embedding of experiment 01.
const coastalView=(name,eye,look,description)=>{
 const world=p=>{const [x,z]=fromBeach(p[0],p[2]);return [x/BUILDING_SCALE,(p[1]+COAST_LIFT)/BUILDING_SCALE,z/BUILDING_SCALE];};
 SHOTS.push({name,title:name,description,duration:40,fov:64,positions:[world(eye),world(eye)],targets:[world(look),world(look)]});
};
coastalView('曲线海岸总览',[1700,5200,.1],[1700,2.55,0],'北 ↑ +y · 东 → +x · 每单位 1 km · 主报告厅 (2, 0)');
coastalView('左环漫滩',[0,4.34,0],[0,3,30],'轻微沙脊起伏 · 潮水浅浅漫过 · 环内环外都是海');
coastalView('主楼沙滩',[2040,16,80],[2000,5,0],'主报告厅 (2, 0) · 沿岸露台与西侧园区');

export const OPENING_OVERVIEW_MS=5000;
export const transitionSeconds=distance=>2*Math.min(6.5,2.2+Math.max(0,distance)*.04);
for(const shot of SHOTS)for(const key of ['positions','targets'])shot[key]=shot[key].map(p=>p.map(v=>v*BUILDING_SCALE));
export function smoothProgress(t){return t*t*t*(10+t*(-15+6*t));}
export function advanceShot(index,time,delta,speed){
  time+=Math.min(.1,Math.max(0,delta))*speed;
  while(time>=SHOTS[index].duration){time-=SHOTS[index].duration;index=(index+1)%SHOTS.length;}
  return {index,time};
}
