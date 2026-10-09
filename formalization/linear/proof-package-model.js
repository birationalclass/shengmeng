export function createProofPackages(nodes){
const byId=new Map(nodes.map(n=>[n.id,n])),roots=byId.get('lemma').overviewRoots||byId.get('lemma').deps,references=[];
const closure=id=>{const out=new Set();function visit(k){if(out.has(k)||!byId.has(k))return;out.add(k);(byId.get(k).overviewSteps||byId.get(k).deps).forEach(visit);}visit(id);return out;};
const owner=new Map(nodes.map(n=>[n.id,'lemma']));for(const r of roots)for(const id of closure(r))if(id!==r)owner.set(id,r);
return {byId,roots,references,owner,closure,members:id=>id==='lemma'?nodes:[...closure(id)].map(k=>byId.get(k)),children:id=>byId.get(id)?.overviewSteps||byId.get(id)?.deps||[],packFor:()=>null};
}
