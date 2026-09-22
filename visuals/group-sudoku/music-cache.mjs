// Compressed bytes only. Bump TRACK_ID whenever the source recording changes.
export const TRACK_ID='magic-study-mp3-v1', CHUNK_SIZE=1024*1024;
export const TRACK_URL=new URL('./audio/magic-study.mp3',import.meta.url).href;
let database;
function open(){
 if(!database)database=new Promise((resolve,reject)=>{
  const request=indexedDB.open('group-sudoku-offline-music',1);
  request.onupgradeneeded=()=>{request.result.createObjectStore('meta');request.result.createObjectStore('chunks');};
  request.onerror=()=>{database=null;reject(request.error);};
  request.onsuccess=()=>{const db=request.result;db.onversionchange=()=>{db.close();database=null;};resolve(db);};
 });
 return database;
}
async function read(store,key){const db=await open();return new Promise((resolve,reject)=>{const r=db.transaction(store).objectStore(store).get(key);r.onsuccess=()=>resolve(r.result);r.onerror=()=>reject(r.error);});}
export const readMeta=()=>read('meta',TRACK_ID);
export const readChunk=index=>read('chunks',[TRACK_ID,index]);
export async function saveChunk(index,blob,meta){
 const db=await open();await new Promise((resolve,reject)=>{
  const tx=db.transaction(['meta','chunks'],'readwrite');
  tx.objectStore('chunks').put(blob,[TRACK_ID,index]);tx.objectStore('meta').put(meta,TRACK_ID);
  tx.oncomplete=resolve;tx.onabort=()=>reject(tx.error||new Error('Storage transaction aborted'));
 });
}
export async function clearTrack(){
 const db=await open();await new Promise((resolve,reject)=>{
  const tx=db.transaction(['meta','chunks'],'readwrite');tx.objectStore('meta').delete(TRACK_ID);
  tx.objectStore('chunks').delete(IDBKeyRange.bound([TRACK_ID,0],[TRACK_ID,Number.MAX_SAFE_INTEGER]));
  tx.oncomplete=resolve;tx.onabort=()=>reject(tx.error||new Error('Storage transaction aborted'));
 });
}
// A single HTTP byte range, including suffix ranges used by media engines.
// Unsupported multi-range requests are ignored, as permitted by HTTP.
export function byteRange(header,size){
 if(!header||header.includes(','))return {start:0,end:size-1,partial:false};
 const match=/^bytes=(\d*)-(\d*)$/.exec(header.trim());
 if(!match||(!match[1]&&!match[2]))return null;
 let start=match[1]?Number(match[1]):Math.max(0,size-Number(match[2]));
 let end=match[1]?(match[2]?Number(match[2]):size-1):size-1;
 if(!Number.isSafeInteger(start)||!Number.isSafeInteger(end)||start<0||start>=size||end<start||(!match[1]&&Number(match[2])===0))return null;
 return {start,end:Math.min(end,size-1),partial:true};
}
export function chunkStream(start,end,getChunk=readChunk){
 let offset=start,cancelled=false;
 return new ReadableStream({
  async pull(controller){
   try{
    if(offset>end){controller.close();return;}
    const index=Math.floor(offset/CHUNK_SIZE),blob=await getChunk(index);
    if(cancelled)return;if(!blob)throw new Error('Offline audio chunk missing');
    const from=offset%CHUNK_SIZE,length=Math.min(blob.size-from,end-offset+1);
    if(length<=0)throw new Error('Offline audio chunk truncated');
    const bytes=new Uint8Array(await blob.slice(from,from+length).arrayBuffer());
    if(cancelled)return;offset+=bytes.length;controller.enqueue(bytes);
   }catch(error){if(!cancelled)controller.error(error);}
  },cancel(){cancelled=true;}
 },{highWaterMark:0});
}
export function offlineResponse(request,meta,getChunk=readChunk){
 const range=byteRange(request.headers.get('Range'),meta.total);
 const headers={'Content-Type':'audio/mpeg','Accept-Ranges':'bytes','Cache-Control':'no-store','X-Sudoku-Audio':'offline'};
 if(!range)return new Response(null,{status:416,headers:{...headers,'Content-Range':`bytes */${meta.total}`}});
 const {start,end,partial}=range;headers['Content-Length']=String(end-start+1);
 if(partial)headers['Content-Range']=`bytes ${start}-${end}/${meta.total}`;
 return new Response(request.method==='HEAD'?null:chunkStream(start,end,getChunk),{status:partial?206:200,headers});
}
