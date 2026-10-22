import {createResourceFetch} from './resource-fetch.js';
import {createBackgroundAssets} from './background-assets.js';
import {chalkInlineRuns} from './chalk-typography.js';
import {prepareBoardAssets} from './board-assets.js';
// Keep downloading the selected course while paused; decode only a small window.
export function createCoursePreload({fetcher=globalThis.fetch,baseURL=new URL('.',import.meta.url).href,concurrency=2,requestTimeout=15000,retryDelay=2000,maxDelay=30000,api=globalThis}={}){
 fetcher=createResourceFetch(fetcher,{idleTimeout:requestTimeout});let wanted=new Set(),runs=new Set(),packed=false,glyphIndex=null,glyphBase=null;
 function needGlyphs(text,add){for(const char of String(text)){wanted.add(char);const glyph=glyphIndex?.get(char);if(glyph)add(new URL(glyph.data,glyphBase).href,'glyph');}}
 const queue=createBackgroundAssets({concurrency,retryDelay,maxDelay,api,load:async(job,signal,add)=>{
  if(job.kind==='boardPack'){await prepareBoardAssets({resourcePack:job.src},{baseURL,background:true,signal,fetcher});return;}
  const r=await fetcher(job.src,{signal,cache:'force-cache',priority:'low'});if(!r.ok)throw Error(r.status+' '+job.src);
  if(job.kind==='atlas'){const m=await r.json();for(const [key,run]of Object.entries(m.runs))if(runs.has(key))add(new URL(run.file,job.src).href);}
  else if(job.kind==='glyphIndex'){const m=await r.json();glyphIndex=new Map(m.glyphs.map(g=>[g.char,g]));glyphBase=job.src;for(const g of m.glyphs)if(wanted.has(g.char))add(new URL(g.data,job.src).href,'glyph');}
  else if(job.kind==='diagram'){const m=await r.json();for(const object of m.objects||[])if(object.type==='label')needGlyphs((object.text||'')+' '+(object.textEn||''),add);}
  else if(job.kind==='glyph'){const m=await r.json();for(const f of [m.ink,m.timeMap])if(f)add(new URL(f,job.src).href);}
  else await r.arrayBuffer();
 }});
 function strings(value){return typeof value==='string'?value:Array.isArray(value)?value.map(strings).join('\n'):value&&typeof value==='object'?Object.values(value).map(strings).join('\n'):'';}
 function start(pages,{courseText}={}){queue.cancel();glyphIndex=null;glyphBase=null;packed=pages.length>0&&pages.every(p=>p.resourcePack);if(packed){pages.forEach(p=>queue.add(new URL(p.resourcePack,baseURL).href,'boardPack'));return queue.run();}const text=courseText??strings(pages);wanted=new Set([...text]);runs=new Set(chalkInlineRuns(text).filter(r=>r.math&&!r.radical).map(r=>r.text));
  const add=(url,kind)=>queue.add(new URL(url,baseURL).href,kind);pages.forEach(p=>{if(p.formulaAsset)add(p.formulaAsset+'?v=report-line-sync-6');const b=p.orderedBoard;if(b){for(const r of b.rows)for(const t of [...(r.tokens||[]),...(r.enTokens||[])])if(t.asset)add(t.asset);if(b.diagramAsset)add(b.diagramAsset,'diagram');}});
  add('./assets/chalk/inline-math/index.json','atlas');add('./assets/chalk/chinese36/index.json?v=rings-glyphs-20261022','glyphIndex');return queue.run();
 }
 return{start,cancel:queue.cancel,retry:queue.retry,get state(){return{...queue.state,unit:packed?'pack':'file'};}};
}
