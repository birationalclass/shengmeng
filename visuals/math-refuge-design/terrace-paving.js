// One grid for the whole terrace. Hall walls are grid lines, so the four
// surrounding areas share the same joints instead of restarting their rows.
export function terracePaving(bounds,hall){
  const [west,east,north,south]=bounds;
  const dx=(hall.east-hall.west)/Math.ceil((hall.east-hall.west)/2.8-1e-9);
  const dz=(hall.south-hall.north)/Math.ceil((hall.south-hall.north)/1.7-1e-9);
  function cuts(min,max,origin,step){
    const result=[min];
    for(let i=Math.floor((min-origin)/step)+1;origin+i*step<max-1e-8;i++){
      const value=origin+i*step;if(value>min+1e-8)result.push(value);
    }
    result.push(max);return result;
  }
  const xs=cuts(west,east,hall.west,dx),zs=cuts(north,south,hall.north,dz),cells=[];
  for(let i=0;i<xs.length-1;i++)for(let j=0;j<zs.length-1;j++){
    const a=xs[i],b=xs[i+1],c=zs[j],d=zs[j+1],x=(a+b)/2,z=(c+d)/2;
    if(x>hall.west&&x<hall.east&&z>hall.north&&z<hall.south)continue;
    cells.push({bounds:[a,b,c,d],column:i,row:j});
  }
  return {cells,xs,zs};
}
