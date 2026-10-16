import {createResourceFetch} from './resource-fetch.js';
// Warm public assets after the cover, without retaining every decoded board canvas.
export function createCoursePreload({fetcher=globalThis.fetch,baseURL=new URL('.',import.meta.url).href,concurrency=2,requestTimeout=15000}={}){
 fetcher=createResourceFetch(fetcher,{idleTimeout:requestTimeout});
 let epoch=0,controllers=new Set(),state={phase:'idle',completed:0,total:0,errors:[]};
 function cancel(){epoch++;controllers.forEach(c=>c.abort());controllers.clear();state={phase:'idle',completed:0,total:0,errors:[]};}
 async function start(pages){cancel();const mine=epoch,queue=[],seen=new Set();state.phase='loading';
  const add=(url,kind='asset')=>{if(mine!==epoch)return;const src=new URL(url,baseURL).href;if(!seen.has(src)){seen.add(src);queue.push({src,kind});state.total++;}};
  pages.forEach(p=>{if(p.formulaAsset)add(p.formulaAsset+'?v=report-line-sync-6');});
  add('./assets/chalk/inline-math/index.json','atlas');add('./assets/chalk/chinese36/index.json?v=section-yue-glyphs-20261015','glyphIndex');
  const text=JSON.stringify(pages),wanted=new Set([...text]);let cursor=0;
  async function read(job){const controller=new AbortController();controllers.add(controller);try{const r=await fetcher(job.src,{signal:controller.signal,cache:'force-cache',priority:'low'});if(!r.ok)throw Error(r.status+' '+job.src);if(job.kind==='atlas'){const m=await r.json();for(const run of Object.values(m.runs))add(new URL(run.file,job.src));}else if(job.kind==='glyphIndex'){const m=await r.json();for(const g of m.glyphs)if(wanted.has(g.char))add(new URL(g.data,job.src),'glyph');}else if(job.kind==='glyph'){const m=await r.json();for(const f of [m.ink,m.timeMap])if(f)add(new URL(f,job.src));}else await r.arrayBuffer();}finally{controllers.delete(controller);}}
  await Promise.all(Array.from({length:concurrency},async()=>{while(mine===epoch&&cursor<queue.length){const job=queue[cursor++];try{await read(job);}catch(e){if(mine===epoch&&e.name!=='AbortError'){state.errors.push(String(e.message));break;}}if(mine===epoch)state.completed++;}}));
  if(mine===epoch)state.phase=state.errors.length?'partial':'ready';return mine===epoch?{...state}:null;
 }
 return{start,cancel,get state(){return{...state,errors:[...state.errors]};}};
}
