const one=result=>Array.isArray(result.data)?result.data[0]:result.data;
function createStore(db,prefix='homework_'){
 const adapter=source=>({
  async get(kind,id){return one(await source.collection(prefix+kind).doc(id).get());},
  async put(kind,id,value){const {_id,...data}=value;if(data.expiresAt)data.expiresOn=new Date(data.expiresAt);await source.collection(prefix+kind).doc(id).set(data);},
  async remove(kind,id){await source.collection(prefix+kind).doc(id).remove();}
 });
 return {...adapter(db),
  async find(kind,where={},limit=100,offset=0){return (await db.collection(prefix+kind).where(where).orderBy('createdAt','desc').skip(offset).limit(limit).get()).data;},
  async ready(){await db.collection(prefix+'users').limit(1).get();},
  transaction:callback=>db.runTransaction(tx=>callback(adapter(tx)))
 };
}
module.exports={createStore};
