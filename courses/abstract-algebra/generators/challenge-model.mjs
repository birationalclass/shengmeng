// Exact closure and minimum generating sets, independent of rendering.
const cache=new WeakMap();
export function closure(group,seeds){const elements=new Set([group.e]),queue=[group.e];for(let i=0;i<queue.length;i++)for(const s of seeds){const x=group.table[queue[i]][s];if(!elements.has(x)){elements.add(x);queue.push(x);}}return elements;}
export function minimumGenerators(group){
 if(cache.has(group))return cache.get(group);
 const n=group.table.length,sets=[];let rank=0;
 function search(start,k,chosen){if(!k){if(closure(group,chosen).size===n)sets.push([...chosen]);return;}for(let x=start;x<=n-k;x++){if(x===group.e)continue;chosen.push(x);search(x+1,k-1,chosen);chosen.pop();}}
 while(!sets.length&&rank<3){rank++;search(0,rank,[]);}
 if(!sets.length)throw Error('Unsupported generating rank');
 const result={rank,sets,eligible:[...new Set(sets.flat())]};cache.set(group,result);return result;
}
export function levels(group){const rank=minimumGenerators(group).rank,n=group.table.length;return n>=12?[{budget:rank+1},{budget:rank},{budget:rank,preset:true}]:n>=8?[{budget:rank+1},{budget:rank}]:[{budget:rank}];}
export function generationRound(group,known){const products=new Map();for(const a of known)for(const b of known){const c=group.table[a][b];if(!known.has(c)&&!products.has(c))products.set(c,{a,b,c});}return [...products.values()];}
export function normalizeJourney(raw,galaxies,groups){const out={};for(const g of galaxies){const count=levels(groups[g.key]).length,r=raw?.[g.key];out[g.key]={passed:Math.max(0,Math.min(count,Math.floor(Number(r?.passed)||0))),times:Array.isArray(r?.times)?r.times.slice(0,count):[]};}return out;}
export function completedCount(journey,galaxies,groups){let n=0;for(const g of galaxies){if((journey[g.key]?.passed||0)<levels(groups[g.key]).length)break;n++;}return n;}
