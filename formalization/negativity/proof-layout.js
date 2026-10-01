// Semantic roots stay in one input rail. Filtering never turns a derived result into a base input.
export function visibleProofIds(nodes,current,scope){
  const byId=new Map(nodes.map(n=>[n.id,n])),ids=new Set([current]);
  function visit(id){if(ids.has(id)&&id!==current)return;ids.add(id);byId.get(id).deps.forEach(visit);}
  if(scope==='direct')byId.get(current).deps.forEach(id=>ids.add(id));
  else if(scope==='path')byId.get(current).deps.forEach(visit);
  else nodes.forEach(n=>{if(scope==='all'||['assumption','pending'].includes(n.status))ids.add(n.id);});
  return ids;
}
export function compactProofLayout(nodes,ids,factor=1,maxRows=4,options={}){
  const byId=new Map(nodes.map(n=>[n.id,n])),ranks=new Map(),layout=new Map();
  function rank(id){if(!ranks.has(id)){const n=byId.get(id);ranks.set(id,n.deps.length?Math.max(0,...n.deps.filter(d=>ids.has(d)).map(rank))+1:0);}return ranks.get(id);}
  [...ids].forEach(rank);
  const roots=nodes.filter(n=>ids.has(n.id)&&!n.deps.length);
  const stacked=roots.length>1&&!options.expandedInputs;
  const active=roots.some(n=>n.id===options.selected)?options.selected:roots.at(-1)?.id;
  let y=85;
  roots.forEach((n,i)=>{
    const compact=stacked&&n.id!==active;
    const visibleH=(compact?48:150)*factor;
    layout.set(n.id,{x:65,y,h:150*factor,visibleH,rank:0,column:0,base:true,compact,stackIndex:i});
    y+=visibleH+(compact?0:18)*factor;
  });
  const bottom=roots.length?layout.get(roots.at(-1).id).y+layout.get(roots.at(-1).id).visibleH:85;
  roots.forEach(n=>{const p=layout.get(n.id);p.h=Math.min(p.h,bottom-p.y);});
  const inputHeight=bottom-85;
  let left=roots.length?465*factor:65;
  const levels=[...new Set([...ranks.values()].filter(r=>r>0))].sort((a,b)=>a-b);
  for(const r of levels){
    const layer=nodes.filter(n=>ids.has(n.id)&&rank(n.id)===r);
    const anchor=n=>{const deps=n.deps.map(id=>layout.get(id)).filter(Boolean);return deps.length?deps.reduce((s,p)=>s+p.y+(p.visibleH||p.h)/2,0)/deps.length:0;};
    layer.sort((a,b)=>anchor(a)-anchor(b));
    const cols=Math.ceil(layer.length/maxRows),groups=Array.from({length:cols},(_,c)=>layer.slice(c*maxRows,(c+1)*maxRows));
    const height=n=>Math.max(150,104+n.deps.length*22)*factor;
    const totals=groups.map(g=>g.reduce((s,n)=>s+height(n)+30*factor,0)-30*factor),full=Math.max(inputHeight,...totals);
    groups.forEach((group,c)=>{let cy=85+(full-totals[c])/2;group.forEach(n=>{const h=height(n);layout.set(n.id,{x:left+c*360*factor,y:cy,h,rank:r,column:c});cy+=h+30*factor;});});
    left+=(cols*360+40)*factor;
  }
  return layout;
}
