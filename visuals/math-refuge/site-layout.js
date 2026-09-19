// Plan axes: east +X, north -Z. Positions use plan units; furniture and
// ceiling heights stay physical after the shared site scale is applied.
export const BUILDING_SCALE=Math.SQRT2;
export const DECK_Y=.28;
export const HALL={west:34.8,east:43.2,north:-4.2,south:4.2,boardX:42.7,clearHeight:3.2};
export const LECTURE_SCALE=.6;
export function configureLectureRoot(root){
  root.scale.setScalar(LECTURE_SCALE);root.rotation.y=-Math.PI/2;
  root.position.set(HALL.boardX*BUILDING_SCALE-10.4*LECTURE_SCALE,DECK_Y*BUILDING_SCALE,-28*LECTURE_SCALE);
}
export const lectureViewOffset=distance=>[-distance*LECTURE_SCALE,0,0];
// A rectangle union, not overlapping reflective planes. The middle branch
// passes through an open-air court, never through the enclosed room floors.
export const POOL_RECTS=[
  [-18,-14,-20,20],[18,22,-20,20],[-14,18,-20,-16],[-14,18,16,20],
  [2,5,-16,16],[22,46,-11,-7],[22,46,7,11],[46,50,-11,11]
];
export const POOL_LEVEL=.20,POOL_DEPTH=1.25/BUILDING_SCALE;
export function inPool(x,z,margin=0){return POOL_RECTS.some(([a,b,c,d])=>x>a-margin&&x<b+margin&&z>c-margin&&z<d+margin);}
export function poolTopology(){
  const xs=[...new Set(POOL_RECTS.flatMap(r=>r.slice(0,2)))].sort((a,b)=>a-b),zs=[...new Set(POOL_RECTS.flatMap(r=>r.slice(2)))].sort((a,b)=>a-b);
  const cells=[],edges=[];
  for(let i=0;i<xs.length-1;i++)for(let j=0;j<zs.length-1;j++){
    const a=xs[i],b=xs[i+1],c=zs[j],d=zs[j+1];if(!inPool((a+b)/2,(c+d)/2))continue;
    cells.push([a,b,c,d]);
    for(const [x1,z1,x2,z2,x,z] of [[a,c,b,c,(a+b)/2,c-.001],[b,c,b,d,b+.001,(c+d)/2],[b,d,a,d,(a+b)/2,d+.001],[a,d,a,c,a-.001,(c+d)/2]])if(!inPool(x,z))edges.push([x1,z1,x2,z2]);
  }
  return {cells,edges};
}
export const BRIDGES=[{x:-16,z:8,span:6,width:2,rise:.28},{x:3.5,z:9,span:5,width:2,rise:.22},{x:20,z:2,span:6,width:2.2,rise:.28}];
export const bridgeHeight=(bridge,t)=>DECK_Y+bridge.rise*Math.sin(Math.PI*Math.max(0,Math.min(1,t)));
export const ROOM_PADS=[[-13.5,1.5,-14,14],[5.5,17.5,-14,14],[-44,-30,-22,-10],[-61,-51,-33,-23],[-52,-42,-43,-33],[-43,-30,14,24]];
export function inBuilding(x,z,margin=0){return ROOM_PADS.some(([a,b,c,d])=>x>a-margin&&x<b+margin&&z>c-margin&&z<d+margin)||(x>HALL.west-margin&&x<HALL.east+margin&&z>HALL.north-margin&&z<HALL.south+margin);}
export const GIANT_TREES=[[-24,26,3],[-51,8,3.6],[-60,-44,3]];
export const BAMBOO_GROVES=[[-25,-29,7,6],[-49,-15,5,8],[-44,30,6,3]];
export const LAWNS=[{x:-4,z:26,rx:15,rz:3},{x:-29,z:5,rx:5,rz:5}];
// The creek stays inland, separate from the hygienic closed pool system.
export const RIVER_NODES=[[-82,25,-40,1.5],[-77,21,-37,1.7],[-74,3,-34,2.2],[-70,1,-25,1.7],[-65,0,-12,1.4],[-59,-.5,5,1.4],[-47,-1,23,1.6],[-33,-1.9,33,1.7],[-10,-3.04,45,2.2]];
const catmull=(a,b,c,d,t)=>.5*((2*b)+(-a+c)*t+(2*a-5*b+4*c-d)*t*t+(-a+3*b-3*c+d)*t*t*t);
export function riverPoint(t){
  const q=Math.max(0,Math.min(1,t))*(RIVER_NODES.length-1),i=Math.min(RIVER_NODES.length-2,Math.floor(q)),f=q-i;
  const a=RIVER_NODES[Math.max(0,i-1)],b=RIVER_NODES[i],c=RIVER_NODES[i+1],d=RIVER_NODES[Math.min(RIVER_NODES.length-1,i+2)];
  return {x:catmull(a[0],b[0],c[0],d[0],f),y:b[1]+(c[1]-b[1])*f,z:catmull(a[2],b[2],c[2],d[2],f),width:b[3]+(c[3]-b[3])*f};
}
const samples=Array.from({length:157},(_,i)=>riverPoint(i/156));
const riverBounds={minX:Math.min(...samples.map(p=>p.x-p.width))-5,maxX:Math.max(...samples.map(p=>p.x+p.width))+5,minZ:Math.min(...samples.map(p=>p.z-p.width))-5,maxZ:Math.max(...samples.map(p=>p.z+p.width))+5};
export function watercourse(x,z){
  if(x<riverBounds.minX||x>riverBounds.maxX||z<riverBounds.minZ||z>riverBounds.maxZ)return {distance:Infinity,y:0,width:0};
  let result={distance:Infinity,y:0,width:0};
  for(let i=0;i<samples.length-1;i++){
    const a=samples[i],b=samples[i+1],dx=b.x-a.x,dz=b.z-a.z;
    const t=Math.max(0,Math.min(1,((x-a.x)*dx+(z-a.z)*dz)/(dx*dx+dz*dz)));
    const distance=Math.hypot(x-a.x-t*dx,z-a.z-t*dz);
    if(distance<result.distance)result={distance,y:a.y+(b.y-a.y)*t,width:a.width+(b.width-a.width)*t};
  }
  return result;
}
export function lawnWeight(x,z){
  let weight=0;
  for(const a of LAWNS){const r=Math.hypot((x-a.x)/a.rx,(z-a.z)/a.rz);weight=Math.max(weight,Math.max(0,Math.min(1,(1-r)*7)));}
  return weight;
}
