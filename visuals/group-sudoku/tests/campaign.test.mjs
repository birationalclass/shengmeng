import assert from 'node:assert/strict';
import test from 'node:test';
import {createRequire} from 'node:module';
import {Campaign,STORAGE_KEY,MAP_STYLE_KEY,clearLocalData} from '../campaign.mjs';
const model=createRequire(import.meta.url)('../../../courses/abstract-algebra/2026-fall/lesson-1/associativity-sudoku.js');
const full=n=>model.completeForced(model.initial(n)).values;
const memory=()=>({value:null,getItem(){return this.value},setItem(key,value){assert.equal(key,STORAGE_KEY);this.value=value}});
test('only verified completion of 3×3 unlocks identity; progress survives reload and replay',()=>{
 const storage=memory(),c=new Campaign(model,storage);assert.equal(c.identityUnlocked,false);
 c.save(2,full(2));assert.deepEqual(c.completed,[2]);assert.equal(c.identityUnlocked,false);
 c.save(3,model.initial(3));assert.equal(c.identityUnlocked,false);
 c.save(3,full(3));assert.equal(c.identityUnlocked,true);
 const reloaded=new Campaign(model,storage);assert.deepEqual(reloaded.completed,[2,3]);assert.deepEqual(reloaded.board(3),full(3));
 reloaded.save(3,model.initial(3));assert.equal(new Campaign(model,storage).identityUnlocked,true);
});
test('reject forged completion, altered clues and malformed boards',()=>{
 const storage=memory();storage.value=JSON.stringify({completed:[3],finished:{3:model.initial(3)},boards:{3:[1]}});
 const c=new Campaign(model,storage);assert.deepEqual(c.completed,[]);assert.deepEqual(c.board(3),model.initial(3));
 const invalid=full(3);invalid[model.initial(3).findIndex(Boolean)]=0;assert.equal(c.save(3,invalid),false);
 const duplicate=full(3),blank=model.initial(3).indexOf(0);duplicate[blank]=duplicate[blank]===1?2:1;c.save(3,duplicate);assert.equal(c.identityUnlocked,false);
 storage.value=JSON.stringify({finished:{3:duplicate}});assert.equal(new Campaign(model,storage).identityUnlocked,false);
});
test('partial entries persist; storage failure never prevents play',()=>{
 const storage=memory(),c=new Campaign(model,storage),v=c.board(6),hint=model.deduction(v);v[hint.target]=hint.value;c.save(6,v);
 assert.deepEqual(new Campaign(model,storage).board(6),v);assert.deepEqual(c.completed,[]);
 const privateMode=new Campaign(model,{getItem(){throw Error('blocked')},setItem(){throw Error('blocked')}});
 assert.equal(privateMode.save(3,full(3)),true);assert.equal(privateMode.identityUnlocked,true);assert.equal(privateMode.persistent,false);
 assert.equal(new Campaign(model).persistent,false);
});

test('regions unlock in sequence and replay preserves mastery',()=>{
 const c=new Campaign(model,memory());assert.equal(c.current,2);assert.equal(c.canEnter(3),false);
 c.save(3,full(3));assert.equal(c.current,2);assert.equal(c.canEnter(4),false);
 c.save(2,full(2));assert.equal(c.current,4);assert.equal(c.canEnter(4),true);assert.equal(c.canEnter(5),false);
 for(let n=4;n<=9;n++)c.save(n,full(n));assert.equal(c.completed.length,8);
 for(let n=2;n<=9;n++)assert.equal(c.canEnter(n),true);
 c.save(4,model.initial(4));assert.equal(c.completed.length,8);assert.equal(c.identityUnlocked,true);
});

 test('clear local data removes only group sudoku records and restores the first level',()=>{
 const data=new Map(),storage={getItem:k=>data.get(k),setItem:(k,v)=>data.set(k,v),removeItem:k=>data.delete(k)};
 const c=new Campaign(model,storage);c.save(2,full(2));c.save(3,full(3));c.save(4,c.board(4));
 data.set(MAP_STYLE_KEY,'mechanical');data.set('other-course-progress','keep');clearLocalData(storage);
 assert.deepEqual([...data],[['other-course-progress','keep']]);const fresh=new Campaign(model,storage);
 assert.equal(fresh.current,2);assert.equal(fresh.identityUnlocked,false);assert.deepEqual(fresh.completed,[]);assert.deepEqual(fresh.board(4),model.initial(4));
 assert.doesNotThrow(()=>clearLocalData(undefined));assert.throws(()=>clearLocalData({removeItem(){throw Error('blocked')}}),/blocked/);
 });

test('inverse unlocks only after level four (5×5), and stays unlocked on replay',()=>{
 const storage=memory(),c=new Campaign(model,storage);for(let n=2;n<=4;n++)c.save(n,full(n));assert.equal(c.inverseUnlocked,false);
 c.save(5,model.initial(5));assert.equal(c.inverseUnlocked,false);c.save(5,full(5));assert.equal(c.inverseUnlocked,true);
 const again=new Campaign(model,storage);assert.equal(again.inverseUnlocked,true);again.save(5,model.initial(5));assert.equal(again.inverseUnlocked,true);
});
