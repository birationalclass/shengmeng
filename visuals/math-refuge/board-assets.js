import {resourceFetch} from './resource-fetch.js';
import {storeBoardAssets,hasPackedAsset} from './board-asset-store.js';
const pending=new Map(),ready=new Map();
export async function prepareBoardAssets(page,{baseURL=new URL('.',import.meta.url).href,background=false,signal,fetcher=resourceFetch}={}){
 if(!page?.resourcePack&&!page?.resourcePacks?.length)return false;
 const packs=page.resourcePacks||[page.resourcePack];await Promise.all(packs.map(async file=>{const src=new URL(file,baseURL).href;
 // A warmed pack is parsed once; individual dependencies are already in the store.
 const cached=ready.get(src);if(cached&&cached.keys.every(k=>hasPackedAsset(k,cached.base)))return true;
 const old=pending.get(src);if(old&&!old.signal?.aborted){if(!background)old.promote?.(src);return old.job;}
 const job=(async()=>{const r=await fetcher(src,{signal,priority:background?'low':'high',cache:'force-cache'});if(!r.ok)throw Error('本板资源包加载失败：'+r.status);const pack=await r.json();if(pack.version!==1||!pack.assets||!pack.base)throw Error('本板资源包无效');const base=new URL(pack.base,src).href;storeBoardAssets(pack.assets,base);ready.set(src,{keys:Object.keys(pack.assets),base});return true;})();pending.set(src,{job,signal,promote:fetcher.promote});
 try{return await job;}finally{if(pending.get(src)?.job===job)pending.delete(src);}
 }));return true;
}
