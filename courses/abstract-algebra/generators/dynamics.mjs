import {collide} from './model.mjs?v=ranked-orbits-16';
export function values(g,elements){return new Map([...elements].map(a=>{const unseen=new Set();for(const b of elements)for(const c of [g.table[a][b],g.table[b][a]])if(!elements.has(c))unseen.add(c);return [a,unseen.size];}));}
export class Growth {
 constructor(g,seeds,random=Math.random){this.g=g;this.elements=new Set(seeds);if(!this.elements.size)throw Error('SEEDS');this.random=random;this.count=0;this.update();}
 update(){this.scores=values(this.g,this.elements);this.done=[...this.scores.values()].every(v=>v===0);}
 plan(){
  this.update();if(this.done)return null;
  const squares=[...this.elements].filter(a=>!this.elements.has(this.g.table[a][a]));
  if(squares.length){const a=squares[Math.floor(this.random()*squares.length)];return {a,b:a,c:this.g.table[a][a],fresh:true};}
  const pickBest=ids=>{const maximum=Math.max(...ids.map(id=>this.scores.get(id)));const tied=ids.filter(id=>this.scores.get(id)===maximum);return tied[Math.floor(this.random()*tied.length)];};
  const ids=[...this.elements],anchor=pickBest(ids);
  const compatible=ids.filter(b=>b!==anchor&&(!this.elements.has(this.g.table[anchor][b])||!this.elements.has(this.g.table[b][anchor])));
  if(!compatible.length)throw Error('Missing productive partner');
  const partner=pickBest(compatible),fresh=[[anchor,partner],[partner,anchor]].filter(([a,b])=>!this.elements.has(this.g.table[a][b]));
  const [a,b]=fresh[Math.floor(this.random()*fresh.length)];return {a,b,c:this.g.table[a][b],fresh:true,anchor,partner,key:[anchor,partner].sort((x,y)=>x-y).join(':')};
 }
 commit(op){const fresh=!this.elements.has(op.c);if(fresh)this.elements.add(op.c);this.count++;this.update();return {...op,fresh,index:this.count};}
}
export function contact(a,b,r,dt=1/120){let dx=b.x-a.x,dy=b.y-a.y,d=Math.hypot(dx,dy);if(d>=2*r)return false;if(d<1e-6){dx=1;dy=0;d=1;}const n={x:dx/d,y:dy/d},overlap=2*r-d,shift=Math.min(overlap*(1-Math.exp(-4*dt))/2,24*dt,a.separationLeft??Infinity,b.separationLeft??Infinity);a.x-=n.x*shift;a.y-=n.y*shift;b.x+=n.x*shift;b.y+=n.y*shift;if(a.separationLeft!==undefined)a.separationLeft-=shift;if(b.separationLeft!==undefined)b.separationLeft-=shift;
 if((a.vx-b.vx)*n.x+(a.vy-b.vy)*n.y>0){const [u,v]=collide({x:a.vx,y:a.vy},{x:b.vx,y:b.vy},n);a.vx=u.x;a.vy=u.y;b.vx=v.x;b.vy=v.y;return true;}return false;}
