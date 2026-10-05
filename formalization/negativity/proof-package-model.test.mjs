import test from 'node:test';
import assert from 'node:assert/strict';
import {nodes} from './graph-data.js';
import {createProofPackages} from './proof-package-model.js';
const model=createProofPackages(nodes);
test('Every audited card has exactly one navigation owner',()=>{
  assert.equal(model.owner.size,nodes.length);
  const legal=new Set(['proper',...model.roots,...model.references.map(p=>'pack:'+p.id)]);
  for(const n of nodes)assert.ok(legal.has(model.owner.get(n.id)),n.id);
});
test('Only H E M are reference packs',()=>assert.deepEqual(model.references.map(p=>p.mark),['H','E','M']));
test('Root modules are actual declarations in the supplied proof',()=>{
  assert.deepEqual(model.children('proper'),['projective','projective2','properiff']);
  for(const id of model.roots){assert.ok(model.byId.get(id).decl);assert.equal(model.byId.get(id).status,'done');}
});
test('Nested proof entries use the exact existing dependencies',()=>{
  for(const n of nodes)if(n.id!=='proper')assert.deepEqual(model.children(n.id),n.deps);
});
test('All cards remain reachable through a module or reference catalog',()=>{
  const reachable=new Set(['proper']);
  for(const root of model.roots)for(const n of model.members(root))reachable.add(n.id);
  for(const p of model.references)for(const n of model.members('pack:'+p.id))reachable.add(n.id);
  assert.equal(reachable.size,nodes.length);
});
test('Reference cards occur in their own pack and no ordinary module catalog',()=>{
  for(const p of model.references)for(const n of p.cards){
    assert.equal(model.owner.get(n.id),'pack:'+p.id);
    for(const root of model.roots)assert.ok(!model.members(root).some(c=>c.id===n.id));
  }
});
test('The finite closure contains every declared prerequisite',()=>{
  for(const n of nodes){const ids=model.closure(n.id);assert.ok(ids.has(n.id));for(const id of ids)for(const dep of model.byId.get(id).deps)assert.ok(ids.has(dep));}
});
