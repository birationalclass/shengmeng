import {collide} from './model.mjs';
export function values(g,elements){return new Map([...elements].map(a=>{const unseen=new Set();for(const b of elements)for(const c of [g.table[a][b],g.table[b][a]])if(!elements.has(c))unseen.add(c);return [a,unseen.size];}));}
export class Growth {
 constructor(g,seeds,random=Math.random){this.g=g;this.elements=new Set(seeds);if(!this.elements.size)throw Error('SEEDS');this.random=random;this.count=0;this.tried=new Set();this.update();}
 update(){this.scores=values(this.g,this.elements);this.done=[...this.scores.values()].every(v=>v===0);}
 plan(){
  this.update();if(this.done)return null;
  const squares=[...this.elements].filter(a=>!this.elements.has(this.g.table[a][a]));
  if(squares.length){const a=squares[Math.floor(this.random()*squares.length)];return {a,b:a,c:this.g.table[a][a],fresh:true};}
  const pairs=[];const ids=[...this.elements];for(let i=0;i<ids.length;i++)for(let j=i+1;j<ids.length;j++){const a=ids[i],b=ids[j],key=[a,b].sort((x,y)=>x-y).join(':');if(!this.tried.has(key))pairs.push({a,b,key,rank:[Math.max(this.scores.get(a),this.scores.get(b)),Math.min(this.scores.get(a),this.scores.get(b))]});}
  pairs.sort((a,b)=>b.rank[0]-a.rank[0]||b.rank[1]-a.rank[1]);
  if(!pairs.length)throw Error('Incomplete closure search');
  const best=pairs.filter(p=>p.rank[0]===pairs[0].rank[0]&&p.rank[1]===pairs[0].rank[1]);const pair=best[Math.floor(this.random()*best.length)];
  const options=[[pair.a,pair.b],[pair.b,pair.a]],fresh=options.filter(([a,b])=>!this.elements.has(this.g.table[a][b]));const [a,b]=(fresh.length?fresh:options)[Math.floor(this.random()*(fresh.length||2))];return {a,b,c:this.g.table[a][b],fresh:!this.elements.has(this.g.table[a][b]),key:pair.key};
 }
 commit(op){const fresh=!this.elements.has(op.c);if(fresh){this.elements.add(op.c);this.tried.clear();}else if(op.key)this.tried.add(op.key);this.count++;this.update();return {...op,fresh,index:this.count};}
}
export function contact(a,b,r){let dx=b.x-a.x,dy=b.y-a.y,d=Math.hypot(dx,dy);if(d>=2*r)return false;if(d<1e-6){dx=1;dy=0;d=1;}const n={x:dx/d,y:dy/d},overlap=2*r-d;a.x-=n.x*overlap/2;a.y-=n.y*overlap/2;b.x+=n.x*overlap/2;b.y+=n.y*overlap/2;
 if((a.vx-b.vx)*n.x+(a.vy-b.vy)*n.y>0){const [u,v]=collide({x:a.vx,y:a.vy},{x:b.vx,y:b.vy},n);a.vx=u.x;a.vy=u.y;b.vx=v.x;b.vy=v.y;return true;}return false;}
