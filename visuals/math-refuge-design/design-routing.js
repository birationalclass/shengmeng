// Shortest rectilinear visibility route, with clearance around all deck envelopes.
export function routeBridge(a,b,buildings,width=3){
 if(!a||!b||a[0]===b[0])return null;
 const rects=buildings.filter(r=>r[8]!=='tree'&&r[8]!=='boat'&&r[8]!=='bench').map(r=>({id:r[0],x:r[4]-r[6]/2-width/2-.3,X:r[4]+r[6]/2+width/2+.3,y:r[5]-r[7]/2-width/2-.3,Y:r[5]+r[7]/2+width/2+.3}));
 const anchors=r=>[[r[4]+r[6]/2,r[5],1,0],[r[4]-r[6]/2,r[5],-1,0],[r[4],r[5]+r[7]/2,0,1],[r[4],r[5]-r[7]/2,0,-1]];
 const blocked=(p,q,ignore=[])=>rects.some(r=>!ignore.includes(r.id)&&(Math.abs(p[0]-q[0])<1e-6?p[0]>r.x+1e-5&&p[0]<r.X-1e-5&&Math.max(p[1],q[1])>r.y+1e-5&&Math.min(p[1],q[1])<r.Y-1e-5:p[1]>r.y+1e-5&&p[1]<r.Y-1e-5&&Math.max(p[0],q[0])>r.x+1e-5&&Math.min(p[0],q[0])<r.X-1e-5));
 let best=null,cost=Infinity;
 for(const s of anchors(a))for(const t of anchors(b)){
  const gap=width/2+.31,p=[s[0]+s[2]*gap,s[1]+s[3]*gap],q=[t[0]+t[2]*gap,t[1]+t[3]*gap];
  if(blocked(s,p,[a[0]])||blocked(t,q,[b[0]]))continue;
  const nodes=[p,q,...rects.flatMap(r=>[[r.x,r.y],[r.x,r.Y],[r.X,r.y],[r.X,r.Y]])];
  // Corners plus endpoint projections allow an orthogonal bend anywhere needed.
  const xs=[...new Set(nodes.map(n=>n[0]))],ys=[...new Set(nodes.map(n=>n[1]))];
  if(xs.length*ys.length>12000)return null;
  const points=[],lookup=new Map();
  for(const x of xs)for(const y of ys)if(!rects.some(r=>x>r.x+1e-5&&x<r.X-1e-5&&y>r.y+1e-5&&y<r.Y-1e-5)){lookup.set(x+','+y,points.length);points.push([x,y]);}
  const start=lookup.get(p+''),end=lookup.get(q+'');if(start===undefined||end===undefined)continue;
  const adj=points.map(()=>[]),rows=new Map(),cols=new Map();points.forEach((n,i)=>{for(const [m,k] of [[rows,n[1]],[cols,n[0]]]){if(!m.has(k))m.set(k,[]);m.get(k).push(i);}});
  for(const [m,axis] of [[rows,0],[cols,1]])for(const ids of m.values()){ids.sort((i,j)=>points[i][axis]-points[j][axis]);for(let k=1;k<ids.length;k++){const i=ids[k-1],j=ids[k];if(!blocked(points[i],points[j])){const d=Math.abs(points[i][axis]-points[j][axis]);adj[i].push([j,d]);adj[j].push([i,d]);}}}
  const dist=points.map(()=>Infinity),prev=[],open=new Set([start]);dist[start]=0;
  while(open.size){let u=-1,v=Infinity;for(const i of open){const score=dist[i]+Math.abs(points[i][0]-q[0])+Math.abs(points[i][1]-q[1]);if(score<v){v=score;u=i;}}if(u===end)break;open.delete(u);for(const [j,d]of adj[u])if(dist[u]+d<dist[j]){dist[j]=dist[u]+d;prev[j]=u;open.add(j);}}
  if(dist[end]<cost){cost=dist[end];const path=[];for(let k=end;k!==undefined;k=prev[k])path.unshift(points[k]);best=[s.slice(0,2),...path,t.slice(0,2)];}
 }
 if(!best)return null;
 return best.filter((p,i)=>i===0||i===best.length-1||Math.abs((p[0]-best[i-1][0])*(best[i+1][1]-p[1])-(p[1]-best[i-1][1])*(best[i+1][0]-p[0]))>1e-6);
}
