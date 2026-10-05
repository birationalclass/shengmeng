export function createProofPackages(nodes){
 const byId=new Map(nodes.map(n=>[n.id,n])),roots=byId.get('lemma').deps,references=[],owner=new Map(nodes.map(n=>[n.id,'lemma']));
 const closure=id=>{const ids=new Set();function visit(k){if(ids.has(k)||!byId.has(k))return;ids.add(k);byId.get(k).deps.forEach(visit);}visit(id);return ids;};
 return {byId,roots,references,owner,closure,members:id=>id==='lemma'?nodes:[],children:id=>id==='lemma'?roots:byId.get(id)?.deps||[],packFor:()=>null};
}
