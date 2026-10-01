// Compact layered layout of a chosen view of the curated DAG. Mathematical edges are unchanged.
export function visibleProofIds(nodes,current,scope){
  const byId=new Map(nodes.map(n=>[n.id,n])),ids=new Set([current]);
  function visit(id){if(ids.has(id)&&id!==current)return;ids.add(id);byId.get(id).deps.forEach(visit);}
  if(scope==='direct')byId.get(current).deps.forEach(id=>ids.add(id));
  else if(scope==='path')byId.get(current).deps.forEach(visit);
  else nodes.forEach(n=>{if(scope==='all'||['assumption','pending'].includes(n.status))ids.add(n.id);});
  return ids;
}
export function compactProofLayout(nodes,ids,factor=1,maxRows=4){
  const byId=new Map(nodes.map(n=>[n.id,n])),ranks=new Map(),layout=new Map();
  function rank(id){if(!ranks.has(id))ranks.set(id,Math.max(-1,...byId.get(id).deps.filter(d=>ids.has(d)).map(rank))+1);return ranks.get(id);}
  [...ids].forEach(rank);let left=65;
  for(let r=0;r<=Math.max(...ranks.values());r++){
    const layer=nodes.filter(n=>ids.has(n.id)&&rank(n.id)===r);
    const anchor=n=>{const deps=n.deps.map(id=>layout.get(id)).filter(Boolean);return deps.length?deps.reduce((s,p)=>s+p.y+p.h/2,0)/deps.length:0;};
    layer.sort((a,b)=>anchor(a)-anchor(b));
    const cols=Math.ceil(layer.length/maxRows),groups=Array.from({length:cols},(_,c)=>layer.slice(c*maxRows,(c+1)*maxRows));
    const height=n=>Math.max(150,104+n.deps.length*22)*factor;
    const totals=groups.map(g=>g.reduce((s,n)=>s+height(n)+30*factor,0)-30*factor),full=Math.max(...totals);
    groups.forEach((group,c)=>{let y=65+(full-totals[c])/2;group.forEach(n=>{const h=height(n);layout.set(n.id,{x:left+c*360*factor,y,h,rank:r,column:c});y+=h+30*factor;});});
    left+=(cols*360+40)*factor;
  }
  return layout;
}
