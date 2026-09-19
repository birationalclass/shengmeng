// Independent shots, not one orbit: aerial reveal, low dolly, interior glide,
// terrace track, aerial retreat. Geometry and durations are original.
export const SHOTS=[
  {name:'山间抵达',title:'在喧嚣之外，<br>留一处思考的地方。',description:'玻璃、光和水，围合一座开放的书院。',duration:24,fov:43,
   positions:[[37,24,41],[31,20,36],[25,16,30],[21,12,26]],targets:[[0,5,0],[0,5,0],[0,4,0],[-1,3,0]]},
  {name:'水庭',title:'让思绪，<br>沿着水面展开。',description:'低位推进 · 水面反射 · 悬浮石阶',duration:22,fov:52,
   positions:[[12,2.25,15],[10,2.2,12],[7.4,2.2,9],[5.2,2.2,5.3]],targets:[[0,3,0],[-2,3,-2],[-3,3,-4],[-3,3,-6]]},
  {name:'书室',title:'没有结论的时候，<br>也可以先坐一会儿。',description:'沿窗漫游 · 书架与黑板 · 开放讨论区',duration:26,fov:59,
   positions:[[-8,2.3,2],[-8,2.3,-1],[-6.5,2.3,-4],[-3,2.3,-5]],targets:[[0,2.5,-6],[1,2.5,-7],[3,2.6,-6],[5,2.6,-5]]},
  {name:'露台',title:'把难题留在纸上，<br>把目光交给远山。',description:'缓慢横移 · 屋顶花园 · 黄昏阅读席',duration:24,fov:48,
   positions:[[8,7.3,7],[4,7.3,6],[-1,7.3,6],[-5,7.3,5.6]],targets:[[-3,7,-2],[-5,7,-1],[-5,7,0],[-8,6.5,5]]},
  {name:'远眺',title:'这里不急着，<br>给每个问题一个答案。',description:'升空退远 · 层叠露台 · 山谷全景',duration:26,fov:43,
   positions:[[18,13,24],[24,18,26],[32,24,23],[40,29,18]],targets:[[0,5,0],[0,5,0],[0,5,0],[0,5,0]]}
];
export function smoothProgress(t){return t*t*(3-2*t);}
export function fadeAt(t){return Math.max(0,1-t/.035,(t-.965)/.035);}
export function advanceShot(index,time,delta,speed){
  time+=Math.min(.1,Math.max(0,delta))*speed;
  while(time>=SHOTS[index].duration){time-=SHOTS[index].duration;index=(index+1)%SHOTS.length;}
  return {index,time};
}
