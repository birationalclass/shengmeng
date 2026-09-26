// Deterministic skeleton tracing for a font preview. The font contains no pen order;
// these paths infer an order from connected centre-lines, not outline traversal.
export function traceInk(alpha,w,h){
 const n=w*h,a=new Uint8Array(n),distance=new Float32Array(n),pixels=[];
 for(let i=0;i<n;i++){a[i]=alpha[i]>28?1:0;distance[i]=a[i]?999:0;if(a[i])pixels.push(i);}
 for(let y=1;y<h-1;y++)for(let x=1;x<w-1;x++){const i=y*w+x;if(a[i])distance[i]=Math.min(distance[i],distance[i-1]+1,distance[i-w]+1,distance[i-w-1]+1.414,distance[i-w+1]+1.414);}
 for(let y=h-2;y>0;y--)for(let x=w-2;x>0;x--){const i=y*w+x;if(a[i])distance[i]=Math.min(distance[i],distance[i+1]+1,distance[i+w]+1,distance[i+w-1]+1.414,distance[i+w+1]+1.414);}
 let changed=true;const offsets=[-w,-w+1,1,w+1,w,w-1,-1,-w-1];
 for(let iteration=0;changed&&iteration<60;iteration++){changed=false;for(let pass=0;pass<2;pass++){const remove=[];for(const i of pixels){if(!a[i]||i<w||i>=n-w||i%w===0||i%w===w-1)continue;const p=offsets.map(o=>a[i+o]),sum=p.reduce((s,v)=>s+v,0);if(sum<2||sum>6)continue;let turns=0;for(let j=0;j<8;j++)if(!p[j]&&p[(j+1)%8])turns++;if(turns!==1)continue;if(pass===0?p[0]*p[2]*p[4]||p[2]*p[4]*p[6]:p[0]*p[2]*p[6]||p[0]*p[4]*p[6])continue;remove.push(i);}for(const i of remove)a[i]=0;if(remove.length)changed=true;}}
 function neighbors(i){const list=[];for(let j=0;j<8;j++){const k=i+offsets[j];if(k<0||k>=n||!a[k]||Math.abs(k%w-i%w)>1)continue;if(j%2&&(a[i+offsets[(j+7)%8]]||a[i+offsets[(j+1)%8]]))continue;list.push(k);}return list;}
 const ink=pixels.filter(i=>a[i]),adj=new Map(ink.map(i=>[i,neighbors(i)])),used=new Set(),paths=[];
 const edge=(i,j)=>Math.min(i,j)*n+Math.max(i,j);
 function walk(start,next){const path=[start];let prev=start,cur=next;used.add(edge(prev,cur));while(true){path.push(cur);const ns=adj.get(cur).filter(k=>k!==prev&&!used.has(edge(cur,k)));if(adj.get(cur).length!==2||!ns.length)break;const k=ns[0];used.add(edge(cur,k));prev=cur;cur=k;}paths.push(path);}
 for(const i of ink){const ns=adj.get(i);if(ns.length===0)paths.push([i,i]);else if(ns.length!==2)for(const j of ns)if(!used.has(edge(i,j)))walk(i,j);}
 for(const i of ink)for(const j of adj.get(i))if(!used.has(edge(i,j)))walk(i,j);
 // Reading bands prevent jumps into later lines. Within each band start at the
 // leftmost glyph, then prefer a nearby endpoint before travelling onward.
 const band=y=>y<85?0:y<180?1:y<285?2:y<390?3:y<465?4:y<555?5:6;
 const groups=Array.from({length:7},()=>[]);for(const p of paths){const ys=p.map(i=>Math.floor(i/w));groups[band(ys.reduce((x,y)=>x+y,0)/ys.length)].push(p);}
 const result=[];for(let row=0;row<7;row++){let remaining=groups[row],last=null;while(remaining.length){let best=0,reverse=false,score=Infinity;const left=Math.min(...remaining.map(p=>Math.min(...p.map(i=>i%w))));for(let j=0;j<remaining.length;j++){const path=remaining[j],min=Math.min(...path.map(i=>i%w));if(min>left+42)continue;for(const rev of [false,true]){const pt=rev?path.at(-1):path[0],x=pt%w,y=Math.floor(pt/w);const value=last?Math.hypot(x-last[0],y-last[1]):x*.8+y*.2;if(value<score){score=value;best=j;reverse=rev;}}}const path=remaining.splice(best,1)[0];if(reverse)path.reverse();const points=path.map(i=>[i%w,Math.floor(i/w)]),widths=path.map(i=>Math.max(2.8,distance[i]*2+2));last=points.at(-1);result.push({points,widths,row,seed:result.length});}}
 return result;
}
if(typeof self!=='undefined'&&typeof self.postMessage==='function'&&typeof document==='undefined')self.onmessage=e=>{try{const start=performance.now(),strokes=traceInk(new Uint8Array(e.data.alpha),e.data.w,e.data.h);self.postMessage({strokes,ms:performance.now()-start});}catch(error){self.postMessage({error:error.message});}};
