const cloudbase=require('@cloudbase/node-sdk');
const {createHandler}=require('./service.cjs');
const {createAI}=require('./ai.cjs');
const app=cloudbase.init({env:process.env.TCB_ENV||process.env.SCF_NAMESPACE}),db=app.database();
const prefix=process.env.REFUGE_PREFIX||'refuge_';
const one=r=>Array.isArray(r.data)?r.data[0]:r.data;
const col=(kind,source=db)=>source.collection(prefix+kind);
const store={
 async aiHistory(userId){return (await col('ai_jobs').where({userId}).orderBy('createdAt','desc').limit(20).get()).data;},
 async update(kind,id,value){await col(kind).doc(id).update(value);},
 async users(after){return (await col('users').where(after?{_id:db.command.gt(after)}:{}).orderBy('_id','asc').limit(51).get()).data;},
 async get(kind,id){return one(await col(kind).doc(id).get());},
 async put(kind,id,value){await col(kind).doc(id).set(kind==='sessions'?{...value,expiresOn:new Date(value.expiresAt)}:value);},
 async remove(kind,id){await col(kind).doc(id).remove();},
 async create(kind,id,value){return db.runTransaction(async tx=>{const ref=col(kind,tx).doc(id);if(one(await ref.get()))return false;await ref.set(value);return true;});},
 async rate(id,expiresAt){return db.runTransaction(async tx=>{const ref=col('limits',tx).doc(id),old=one(await ref.get()),count=(old?.count||0)+1;await ref.set({count,expiresAt:new Date(expiresAt)});return count;});},
 async messages(){return (await col('messages').orderBy('createdAt','desc').limit(50).get()).data;}
};
const handle=createHandler(store,{ai:createAI(store),cookieName:prefix==='refuge_test_'?'refuge_test_session':'refuge_session',origins:(process.env.REFUGE_ORIGINS||'https://birationalclass.github.io').split(',')});
exports.main=(event,context)=>{const trusted=cloudbase.getCloudbaseContext(context);return handle({...event,trustedIp:trusted.TCB_SOURCE_IP||event.requestContext?.identity?.sourceIp||'gateway'});};
