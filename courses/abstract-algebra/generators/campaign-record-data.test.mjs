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
