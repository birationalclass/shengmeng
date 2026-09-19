// Split overlapping architectural rectangles into a watertight union. Each
// horizontal area is rendered once: intersecting paths cannot depth-fight.
export function platformUnion(rects){
  const unique=values=>[...new Set(values)].sort((a,b)=>a-b);
  const xs=unique(rects.flatMap(r=>r.slice(0,2))),zs=unique(rects.flatMap(r=>r.slice(2)));
  const contains=(x,z)=>rects.some(([a,b,c,d])=>x>a&&x<b&&z>c&&z<d);
  const cells=[],edges=[];
  for(let i=0;i<xs.length-1;i++)for(let j=0;j<zs.length-1;j++){
    const a=xs[i],b=xs[i+1],c=zs[j],d=zs[j+1];
    if(b-a<1e-7||d-c<1e-7||!contains((a+b)/2,(c+d)/2))continue;
    cells.push([a,b,c,d]);
    for(const [x1,z1,x2,z2,x,z] of [[a,c,b,c,(a+b)/2,c-1e-6],[b,c,b,d,b+1e-6,(c+d)/2],[b,d,a,d,(a+b)/2,d+1e-6],[a,d,a,c,a-1e-6,(c+d)/2]]){
      if(!contains(x,z))edges.push([x1,z1,x2,z2]);
    }
  }
  return {cells,edges};
}
