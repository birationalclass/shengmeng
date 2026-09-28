export const DISK_STYLES=[
 ['双臂织光','M51'],['长棒回旋','NGC 1300'],['絮羽星河','NGC 2841'],['车轮回声','Cartwheel'],['潮汐之翼','Arp 142'],
 ['四臂流萤','spiral'],['断弦','flocculent'],['偏心之环','ring'],['镜湖','lenticular'],['星汐双湾','tidal'],
 ['三叶旋歌','spiral'],['银丝涡','spiral'],['北斗引航','Big Dipper · 大熊座星群'],['仙后之冠','Cassiopeia'],['猎户之门','Orion'],['天鹅十字','Cygnus'],['天蝎长钩','Scorpius'],['狮心镰月','Leo'],['双子相望','Gemini'],['南十字光标','Crux']
];
// Stylized familiar star patterns, not equatorial coordinate charts.
export const CONSTELLATIONS={
 12:{nodes:[[-9,2],[-6,0],[-3,1],[0,3],[5,2],[6,6],[1,7]],edges:[[0,1],[1,2],[2,3],[3,4],[4,5],[5,6],[6,3]]},
 13:{nodes:[[-9,-4],[-5,4],[0,-2],[5,5],[9,-4]],edges:[[0,1],[1,2],[2,3],[3,4]]},
 14:{nodes:[[-5,-7],[5,-6],[-2,-1],[0,0],[2,1],[-4,8],[5,8],[-1,-10]],edges:[[0,2],[2,3],[3,4],[4,1],[2,5],[4,6],[0,7],[7,1],[5,6]]},
 15:{nodes:[[0,-10],[0,-2],[0,3],[0,10],[-8,-1],[8,2]],edges:[[0,1],[1,2],[2,3],[4,1],[1,5]]},
 16:{nodes:[[-6,-8],[-8,-5],[-5,-3],[-2,-1],[1,3],[2,7],[6,9],[9,7],[9,4],[7,3]],edges:[[0,2],[1,2],[2,3],[3,4],[4,5],[5,6],[6,7],[7,8],[8,9]]},
 17:{nodes:[[5,-8],[1,-9],[-3,-6],[-4,-2],[0,1],[1,5],[-8,7],[-9,3]],edges:[[0,1],[1,2],[2,3],[3,4],[4,5],[5,6],[6,7],[7,4]]},
 18:{nodes:[[-5,-8],[4,-9],[-4,-3],[4,-3],[-6,2],[-2,2],[2,3],[7,2],[-7,8],[-1,9],[1,9],[8,8]],edges:[[0,2],[1,3],[2,3],[2,4],[2,5],[3,6],[3,7],[4,8],[5,9],[6,10],[7,11]]},
 19:{nodes:[[0,-9],[0,-2],[1,10],[-5,-2],[6,-1]],edges:[[0,1],[1,2],[3,1],[1,4]]}
};
function constellationPoints(style,count,inner,outer,rand,normal){
 const {nodes,edges}=CONSTELLATIONS[style],out=[],unit=outer/14;
 for(let i=0;i<count;i++){
  let x,z;if(i%3===0){const n=nodes[Math.floor(rand()*nodes.length)];x=n[0]+normal()*.32;z=n[1]+normal()*.32;}
  else {const [a,b]=edges[Math.floor(rand()*edges.length)],u=rand();x=nodes[a][0]*(1-u)+nodes[b][0]*u+normal()*.24;z=nodes[a][1]*(1-u)+nodes[b][1]*u+normal()*.24;}
  // Offset the central void below the pattern instead of wrapping its outline into a ring.
  x*=unit;z=(z-1)*unit;const r=Math.hypot(x,z);
  if(r<inner||r>outer){i--;continue;}out.push(x,0,z);
 }return out;
}
export function diskPoints(style,count=7600,inner=3,outer=20){let seed=811+style*173;const rand=()=>{seed=seed*16807%2147483647;return(seed-1)/2147483646;},normal=()=>Math.sqrt(-2*Math.log(Math.max(1e-8,rand())))*Math.cos(Math.PI*2*rand()),out=[];
 if(CONSTELLATIONS[style])return constellationPoints(style,count,inner,outer,rand,normal);
 for(let i=0;i<count;i++){let u=rand(),a=rand()*Math.PI*2;const type=style%5,arm=i%([2,2,7,8,2][type]),twist=[5.4,3.1,7.7,1.2,2.4][type]+Math.floor(style/5)*.8;
 if(type===0){u=Math.pow(u,.8);a=arm*Math.PI+twist*u+normal()*(.08+.15*u);if(style===5)a=(i%4)*Math.PI/2+u*2.6+normal()*.15;if(style===10)a=(i%3)*Math.PI*2/3+u*4+normal()*.13;}
 if(type===1){a=(i%2)*Math.PI+Math.max(0,u-.35)*twist*2+normal()*(.04+.15*u);if(style===6&&i%5===0){a+=1.2;u*=.7;}}
 if(type===2){const segment=i%13;u=Math.max(0,Math.min(1,segment/13+normal()*.07));a=segment*2.39996+u*twist+normal()*.18;if(style===7){u=.7+normal()*.07;a=rand()*Math.PI*2;}}
 if(type===3){u=(i%3===0?.32:.8)+normal()*.055;if(style===8)u=Math.sqrt(rand());if(style===18)a=(rand()-.5)*Math.PI*1.5+u;}
 if(type===4){a=(i%2)*Math.PI+u*twist+normal()*.13;u=Math.pow(u,.55);if(style===14)a=u*4+normal()*.2;if(style===19)a=(i%5)*Math.PI*2/5+u*6+normal()*.13;}
 // Diffuse inter-arm stars prevent the footprint becoming only line art.
 if(i%9===0){u=Math.sqrt(rand());a=rand()*Math.PI*2;}
 u=Math.max(.002,Math.min(.998,u));const r=inner+(outer-inner)*u;out.push(Math.cos(a)*r,0,Math.sin(a)*r);
 }return out;
}
