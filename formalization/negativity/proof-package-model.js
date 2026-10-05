import {sourcePackFor,buildSourcePacks} from './source-pack-catalog.js?v=20261004-packs-46';

// Navigation groups are reading structure, never additional proof dependencies.
export function createProofPackages(nodes){
  const byId=new Map(nodes.map(n=>[n.id,n]));
  const roots=['projective','projective2','properiff'].filter(id=>byId.has(id));
  const references=buildSourcePacks(nodes),owner=new Map();
  const closure=id=>{const ids=new Set();function visit(key){if(ids.has(key)||!byId.has(key))return;ids.add(key);byId.get(key).deps.forEach(visit);}visit(id);return ids;};
  for(const pack of references)for(const n of pack.cards)owner.set(n.id,'pack:'+pack.id);
  for(const root of roots)for(const id of closure(root))if(!owner.has(id))owner.set(id,root);
  for(const n of nodes)if(!owner.has(n.id))owner.set(n.id,n.id==='proper'?'proper':n.paper==='fiber'?'projective2':['projective','antiample','support'].includes(n.paper)?'projective':'properiff');
  const members=id=>id.startsWith('pack:')?(references.find(p=>'pack:'+p.id===id)?.cards||[]):nodes.filter(n=>owner.get(n.id)===id);
  const children=id=>id==='proper'?roots:byId.get(id)?.deps||[];
  const packFor=id=>references.find(p=>p.id===id);
  return {byId,roots,references,owner,closure,members,children,packFor};
}
