// Overview membership is editorial display data; deps remains the Lean proof route.
export function createProofPackages(nodes){
  const byId=new Map(nodes.map(n=>[n.id,n])),root=byId.get('lemma'),references=[];
  const closure=id=>{const out=new Set();function visit(k){if(out.has(k)||!byId.has(k))return;out.add(k);byId.get(k).deps.forEach(visit);}visit(id);return out;};
  const frontier=id=>{
    const seen=new Set(),result=[];
    function visit(k){if(seen.has(k))return;seen.add(k);const n=byId.get(k);if(!n)return;
      if(n.displayRole==='wrapper'&&n.deps.length)n.deps.forEach(visit);else result.push(k);}
    (byId.get(id)?.deps||[]).forEach(visit);return result;
  };
  const roots=[...new Set(root.overview||frontier(root.id))].filter(id=>id!==root.id&&byId.has(id));
  const owner=new Map(nodes.map(n=>[n.id,'lemma']));
  for(const r of roots)for(const id of closure(r))if(id!==r&&!roots.includes(id))owner.set(id,r);
  return {byId,roots,references,owner,closure,
    members:id=>id==='lemma'?nodes:[...closure(id)].map(k=>byId.get(k)),
    children:id=>byId.get(id)?.deps||[],
    isPackage:id=>byId.get(id)?.displayRole!=='wrapper'&&frontier(id).length>=2,
    packFor:()=>null};
}
