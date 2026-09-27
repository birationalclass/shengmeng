// Completed bytes occupy the transfer budget; decoding/building have separate budgets.
export async function fetchProgressBlob(url,onProgress=()=>{},fetcher=fetch){
 const response=await fetcher(url);
 if(!response.ok)throw new Error(`Resource HTTP ${response.status}`);
 const size=Number(response.headers.get('content-length')),encoded=response.headers.get('content-encoding');
 if(!response.body?.getReader){const blob=await response.blob();onProgress(1);return blob;}
 const reader=response.body.getReader(),chunks=[];let received=0;
 try{for(;;){const {done,value}=await reader.read();if(done)break;chunks.push(value);received+=value.byteLength;
   if(size>0&&!encoded)onProgress(Math.min(.99,received/size));
 }}finally{reader.releaseLock();}
 onProgress(1);return new Blob(chunks,{type:response.headers.get('content-type')||'application/octet-stream'});
}
