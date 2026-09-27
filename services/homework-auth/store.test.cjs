const test=require('node:test'),assert=require('node:assert/strict');
const {createStore}=require('./store.cjs');
test('CloudBase writes omit reserved _id and retain TTL metadata in transactions',async()=>{
 let written;const source={collection:()=>({doc:()=>({set:async data=>{assert.ok(!('_id' in data));written=data;}})})};
 const db={...source,runTransaction:fn=>fn(source)},store=createStore(db);
 await store.transaction(tx=>tx.put('sessions','fixture',{_id:'fixture',expiresAt:1234,hash:'fixture'}));
 assert.equal(written.expiresOn.getTime(),1234);assert.equal(written.hash,'fixture');
});
