import test from 'node:test';
import assert from 'node:assert/strict';
import {groups,validate,Closure,collide} from './model.mjs';
function run(g,seeds){const e=new Closure(g,seeds),ops=[];while(!e.done){const op=e.next();if(op)ops.push(op);assert.ok(ops.length<2000);}return {e,ops};}
test('all preset tables are groups',()=>{for(const g of Object.values(groups))assert.equal(validate(g.table,120),g.e);});
test('S3 generators generate six, with every ordered pair and a final stable round',()=>{const {e,ops}=run(groups.S3,[1,2]);assert.equal(e.elements.size,6);assert.deepEqual(ops.filter(o=>o.round===1).map(o=>[o.a,o.b]),[[1,1],[1,2],[2,1],[2,2]]);assert.equal(ops.filter(o=>o.round===e.round).length,36);assert.ok(ops.filter(o=>o.round===e.round).every(o=>!o.fresh));assert.equal(new Set(ops.filter(o=>o.fresh).map(o=>o.c)).size,4);});
test('new elements do not join their discovery round',()=>{const {ops}=run(groups.S3,[1,2]);for(const o of ops.filter(o=>o.fresh))assert.ok(ops.filter(p=>p.round===o.round).every(p=>p.a!==o.c&&p.b!==o.c));});
test('proper cyclic subgroup and identity alone',()=>{assert.deepEqual([...run(groups.C6,[2]).e.elements].sort(),[0,2,4]);assert.deepEqual([...run(groups.S3,[0]).e.elements],[0]);assert.throws(()=>new Closure(groups.C6,[]),/SEEDS/);});
test('noncommutativity and other presets',()=>{assert.notEqual(groups.S3.table[1][2],groups.S3.table[2][1]);assert.equal(run(groups.D4,[1,4]).e.elements.size,8);assert.equal(run(groups.Q8,[2,4]).e.elements.size,8);});
test('custom group validation rejects invalid inputs',()=>{assert.equal(validate([[0,1],[1,0]]),0);assert.throws(()=>validate([[0,2],[1,0]]),/SIZE/);assert.throws(()=>validate([[1,0],[1,0]]),/IDENTITY/);assert.throws(()=>validate([[0,1],[1,1]]),/INVERSE/);});
test('equal mass collision conserves momentum and energy',()=>{const a={x:3,y:2},b={x:-1,y:5},[u,v]=collide(a,b,{x:1,y:0});assert.deepEqual(u,{x:-1,y:2});assert.deepEqual(v,{x:3,y:5});assert.equal(u.x+v.x,a.x+b.x);assert.equal(u.y+v.y,a.y+b.y);assert.equal(u.x**2+u.y**2+v.x**2+v.y**2,a.x**2+a.y**2+b.x**2+b.y**2);});
