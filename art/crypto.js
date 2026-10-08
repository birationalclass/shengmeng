const encoder = new TextEncoder();
const decoder = new TextDecoder();
export function shanghaiDate(date = new Date()) {
  const p = Object.fromEntries(new Intl.DateTimeFormat('en-CA', {timeZone:'Asia/Shanghai',year:'numeric',month:'2-digit',day:'2-digit'}).formatToParts(date).filter(x=>x.type!=='literal').map(x=>[x.type,x.value]));
  return {stamp:`${p.year}-${p.month}-${p.day}`, product:Number(p.month)*Number(p.day)};
}
export function dailyPassword(date = new Date()) { return `Fujita${shanghaiDate(date).product}`; }
const bytes = s => Uint8Array.from(atob(s), c=>c.charCodeAt(0));
async function slot(password) { return Array.from(new Uint8Array(await crypto.subtle.digest('SHA-256',encoder.encode(password))),x=>x.toString(16).padStart(2,'0')).join('').slice(0,24); }
export async function unlockVault(password,vault,date = new Date()) {
  if(password!==dailyPassword(date)) throw new Error('密码不正确。');
  const wrap=vault.wraps[await slot(password)];
  if(!wrap) throw new Error('密码不正确。');
  const material=await crypto.subtle.importKey('raw',encoder.encode(password),'PBKDF2',false,['deriveKey']);
  const wrapping=await crypto.subtle.deriveKey({name:'PBKDF2',hash:'SHA-256',salt:bytes(vault.salt),iterations:vault.iterations},material,{name:'AES-GCM',length:256},false,['decrypt']);
  const raw=new Uint8Array(await crypto.subtle.decrypt({name:'AES-GCM',iv:bytes(wrap.iv)},wrapping,bytes(wrap.data)));
  const key=await crypto.subtle.importKey('raw',raw,{name:'AES-GCM'},false,['decrypt']);raw.fill(0);
  const plaintext=await crypto.subtle.decrypt({name:'AES-GCM',iv:bytes(vault.manifest.iv)},key,bytes(vault.manifest.data));
  return {key,manifest:JSON.parse(decoder.decode(plaintext)),stamp:shanghaiDate(date).stamp};
}
export async function loadAsset(asset,key,onProgress=()=>{},signal) {
  const parts=new Array(asset.chunks.length);let loaded=0,cursor=0;
  async function worker(){
    while(cursor<asset.chunks.length){
      const i=cursor++,chunk=asset.chunks[i];
      const r=await fetch(chunk.url,{signal});if(!r.ok)throw new Error('文件加载失败，请重试。');
      const encrypted=await r.arrayBuffer();
      if(signal?.aborted)throw new DOMException('Aborted','AbortError');
      const plain=await crypto.subtle.decrypt({name:'AES-GCM',iv:bytes(chunk.iv),additionalData:encoder.encode(`${asset.id}:${i}:${chunk.size}`)},key,encrypted);
      if(plain.byteLength!==chunk.size)throw new Error('文件校验失败。');
      parts[i]=plain;loaded+=chunk.size;onProgress(loaded/asset.size);
    }
  }
  await Promise.all(Array.from({length:Math.min(3,asset.chunks.length)},worker));
  if(signal?.aborted)throw new DOMException('Aborted','AbortError');
  const blob=new Blob(parts,{type:asset.type});if(blob.size!==asset.size)throw new Error('文件校验失败。');return blob;
}
export async function loadPart(asset,index,key,signal) {
  const chunk=asset.chunks[index];if(!chunk)throw new Error('视频片段不存在。');
  const response=await fetch(chunk.url,{signal});if(!response.ok)throw new Error('视频加载失败，请重试。');
  const data=await response.arrayBuffer();if(signal?.aborted)throw new DOMException('Aborted','AbortError');
  const plain=chunk.iv?await crypto.subtle.decrypt({name:'AES-GCM',iv:bytes(chunk.iv),additionalData:encoder.encode(`${asset.id}:${index}:${chunk.size}`)},key,data):data;
  if(plain.byteLength!==chunk.size)throw new Error('视频片段校验失败。');return plain;
}
