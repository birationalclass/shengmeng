import test from 'node:test';
import assert from 'node:assert/strict';
import {ownRecordIndex} from './campaign-record-data.mjs';
test('guest identity matches uniquely without relying on ranking',()=>{
 const rows=[{kind:'guest',name:'游客 OTHER'},{kind:'guest',name:'游客 ME'}];
 assert.equal(ownRecordIndex(rows,{id:'guest_123',kind:'guest',name:'ME'}),1);
 assert.equal(ownRecordIndex([...rows,rows[1]],{id:'guest_123',kind:'guest',name:'ME'}),-1);
});
test('student needs matching masked id and initials; ambiguous identities stay unmarked',()=>{
 const account={id:'12345678901',kind:'student',name:'测试',initials:'CS'};
 const row={kind:'student',studentId:'123****8901',name:'CS'};
 assert.equal(ownRecordIndex([row],account),0);
 assert.equal(ownRecordIndex([row,{...row}],account),-1);
 assert.equal(ownRecordIndex([{...row,name:'OTHER'}],account),-1);
});
test('local records use exact account id',()=>{
 assert.equal(ownRecordIndex([{id:'mine',kind:'guest',name:''}],{id:'mine',kind:'guest'}),0);
 assert.equal(ownRecordIndex([{id:'other',kind:'guest',name:'same'}],{id:'mine',kind:'guest',name:'same'}),-1);
});

test('own newer local progress remains visible without adding other local players',async()=>{
 const {withOwnLocalRecord}=await import('./campaign-record-data.mjs');
 const account={id:'guest_me',kind:'guest',name:'ME'},local={...account,highest:6,completedLevels:9};
 const rows=withOwnLocalRecord([{kind:'guest',name:'游客 ME',highest:2,completedLevels:3,consumedLives:4}],local,account);
 assert.equal(rows.length,1);assert.equal(rows[0].highest,6);assert.equal(rows[0].localOnly,true);assert.equal(rows[0].consumedLives,4);
 assert.equal(withOwnLocalRecord([],local,account)[0].localOnly,true);
 assert.equal(withOwnLocalRecord([{kind:'guest',name:'游客 ME',highest:7,completedLevels:12}],local,account)[0].localOnly,undefined);
});
