// A genuine C4 action: three fixed points, one 2-cycle and one 4-cycle.
export const ORBIT_EXAMPLE={p:2,groupOrder:4,generator:[0,1,2,4,3,6,7,8,5],orbits:[[0],[1],[2],[3,4],[5,6,7,8]],boxedOrbit:4};
export function orbitDiagram(ctx,{stroke,label}){
 const path=(points,color,width=2.8)=>stroke(points,color,width);
 const smooth=(points,color)=>{const out=[];for(let i=0;i<points.length-1;i++){const a=points[i],b=points[i+1];for(let j=0;j<15;j++){const t=j/15;out.push([a[0]+(b[0]-a[0])*t,a[1]+(b[1]-a[1])*t+9*Math.sin(t*Math.PI)]);}}out.push(points.at(-1));path(out,color);};
 const dot=(x,y,c)=>{path(Array.from({length:25},(_,i)=>[x+4.5*Math.cos(i/24*Math.PI*2),y+4.5*Math.sin(i/24*Math.PI*2)]),c,4);};
 const boundary=Array.from({length:85},(_,i)=>{const t=i/84*Math.PI*2;return[1210+237*Math.cos(t)*(1+.018*Math.sin(3*t)),321+173*Math.sin(t)];});path(boundary,'#ddd8bf');
 label('X',1428,171,38,'#ddd8bf');label('H=C₄, p=2',1053,117,30,'#eee9d5');label('|X|=9',1153,535,30,'#eee9d5');
 const colors=['#93c9ff','#e4cf9c','#b9d9ac','#d8b4e8','#efb29a'];
 [[1060,218],[1195,198],[1330,223]].forEach(([x,y],i)=>dot(x,y,colors[i]));
 smooth([[1045,293],[1120,278],[1193,301]],colors[3]);[[1045,293],[1193,301]].forEach(([x,y])=>dot(x,y,colors[3]));
 const four=[[1056,390],[1165,372],[1262,398],[1370,377]];smooth(four,colors[4]);four.forEach(([x,y])=>dot(x,y,colors[4]));
 // A dashed orbit set, with an arrow identifying the orbit of x.
 const corners=[[1024,347],[1400,347],[1400,426],[1024,426],[1024,347]];
 for(let i=0;i<4;i++){const a=corners[i],b=corners[i+1],length=Math.hypot(b[0]-a[0],b[1]-a[1]);for(let at=0;at<length;at+=19){const u=at/length,v=Math.min(length,at+10)/length;path([[a[0]+(b[0]-a[0])*u,a[1]+(b[1]-a[1])*u],[a[0]+(b[0]-a[0])*v,a[1]+(b[1]-a[1])*v]],colors[4],2);}}
 label('x',1043,374,24,colors[4]);path([[1170,449],[1170,433]],colors[4],2);path([[1164,442],[1170,433],[1176,442]],colors[4],2);label('|H·x|=4',1100,475,28,colors[4]);
}
