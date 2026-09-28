import test from 'node:test';import assert from 'node:assert/strict';
import {GALAXIES,progress,unlocked,complete} from './galaxy-campaign.mjs';import {groups} from './model.mjs';
test('every galaxy contains exactly as many main planets as its group order',()=>{for(const g of GALAXIES)assert.equal(g.order,groups[g.key].labels.length);assert.equal(GALAXIES[0].key,'C4');assert.equal(GALAXIES[1].key,'S3');});
test('demo journey unlocks sequentially and rejects locked completions',()=>{let done=0;assert.ok(unlocked(0,done));assert.equal(unlocked(1,done),false);assert.equal(complete(4,done),0);for(let i=0;i<GALAXIES.length;i++){done=complete(i,done);assert.equal(done,i+1);if(i+1<GALAXIES.length)assert.ok(unlocked(i+1,done));}assert.equal(complete(0,done),7);assert.equal(unlocked(7,done),false);});
test('invalid local progress cannot unlock unbounded or negative sectors',()=>{assert.equal(progress(-10),0);assert.equal(progress('bad'),0);assert.equal(progress(100),7);});
