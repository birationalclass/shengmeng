// Page packs prime the exact existing loaders. Rendering and stroke semantics stay shared.
const assets=new Map();let bytes=0;const LIMIT=16*1024*1024;
const key=(url,base)=>{const u=new URL(String(url),base);u.search='';u.hash='';return u.href;};
export function storeBoardAssets(entries,base){
 for(const [url,item]of Object.entries(entries)){const id=key(url,base),prior=assets.get(id);if(prior)bytes-=prior.size;const size=item.encoding==='base64'?item.body.length*3/4:item.body.length*2;assets.delete(id);assets.set(id,{...item,size});bytes+=size;}
 while(bytes>LIMIT&&assets.size){const id=assets.keys().next().value;bytes-=assets.get(id).size;assets.delete(id);}
}
export function packedAssetResponse(url,base=globalThis.location?.href){
 if(!base)return null;let id;try{id=key(url,base);}catch{return null;}const asset=assets.get(id);if(!asset)return null;assets.delete(id);assets.set(id,asset);
 const body=asset.encoding==='base64'?Uint8Array.from(atob(asset.body),c=>c.charCodeAt(0)):asset.body;
 return new Response(body,{headers:{'Content-Type':asset.type}});
}
export function hasPackedAsset(url,base){return assets.has(key(url,base));}
export function boardAssetStoreState(){return{files:assets.size,bytes};}
