import {fail} from '../cloudflare/worker.mjs';
const one=result=>Array.isArray(result.data)?result.data[0]:result.data;
export function createStore(db,prefix='sudoku_'){
 const collection=(name,source=db)=>source.collection(prefix+name);
 return {
  async ready(){return (await collection('students').limit(1).get()).data.length>0;},
  async student(id){return one(await collection('students').doc(id).get());},
  async records(){
   const rows=[];for(let offset=0;;offset+=100){const batch=(await collection('completions').orderBy('_id','asc').skip(offset).limit(100).get()).data;rows.push(...batch);if(batch.length<100)break;}return rows;
  },
  async rate(key,minute){
   return db.runTransaction(async tx=>{
    const ref=collection('limits',tx).doc(key),old=one(await ref.get());
    const count=old?.minute===minute?old.count+1:1;
    await ref.set({minute,count,expiresAt:new Date((minute+1440)*60000)});return count;
   });
  },
  async save(student,input,at){
   return db.runTransaction(async tx=>{
    const request=collection('requests',tx).doc(input.submissionId),completion=collection('completions',tx).doc(student.id);
    const oldRequest=one(await request.get()),old=one(await completion.get());
    if(oldRequest&&oldRequest.studentId!==student.id)throw fail(409,'提交编号已使用。');
    if(oldRequest){if(!old)throw Error('missing completion');return old;}
    const record={id:student.id,name:student.name,initials:student.initials,first_at:old?.first_at||at,updated_at:at};
    await request.set({studentId:student.id,createdAt:at,boards:input.boards});
    await completion.set(record);return record;
   });
  }
 };
}
