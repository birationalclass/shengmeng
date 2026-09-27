export function validate(table,limit=16) {
  const n=table.length;
  if(n<1||n>limit||table.some(r=>r.length!==n||r.some(x=>!Number.isInteger(x)||x<0||x>=n))) throw Error('SIZE');
  const e=table.findIndex((r,i)=>r.every((x,j)=>x===j&&table[j][i]===j));
  if(e<0) throw Error('IDENTITY');
  for(let a=0;a<n;a++) {
    if(!table[a].some((x,b)=>x===e&&table[b][a]===e)) throw Error('INVERSE');
    for(let b=0;b<n;b++) for(let c=0;c<n;c++) if(table[table[a][b]][c]!==table[a][table[b][c]]) throw Error('ASSOCIATIVE');
  }
  return e;
}
function group(name,labels,multiply){const table=labels.map((_,a)=>labels.map((_,b)=>multiply(a,b)));return {name,labels,table,e:validate(table,120)};}
export const groups={
  C6:group('C₆',['e','r','r²','r³','r⁴','r⁵'],(a,b)=>(a+b)%6),
  S3:group('S₃',['e','(12)','(23)','(13)','(123)','(132)'],(a,b)=>{
    const p=[[0,1,2],[1,0,2],[0,2,1],[2,1,0],[1,2,0],[2,0,1]];
    return p.findIndex(q=>q.every((x,i)=>x===p[a][p[b][i]]));
  }),
  D4:group('D₄',['e','r','r²','r³','s','rs','r²s','r³s'],(a,b)=>((a%4+(a<4?1:-1)*(b%4)+4)%4)+4*((Math.floor(a/4)+Math.floor(b/4))%2)),
  Q8:group('Q₈',['1','−1','i','−i','j','−j','k','−k'],(a,b)=>{
    const units=[[0,2,4,6],[2,1,6,5],[4,7,1,2],[6,4,3,1]];
    return units[Math.floor(a/2)][Math.floor(b/2)]^(a%2)^(b%2);
  })
};
function symmetric(n){
 const permutations=[];function build(prefix,left){if(!left.length){permutations.push(prefix);return;}for(const x of left)build([...prefix,x],left.filter(y=>y!==x));}build([],Array.from({length:n},(_,i)=>i));
 const index=new Map(permutations.map((p,i)=>[p.join(','),i]));
 const labels=permutations.map(p=>{const seen=new Set(),cycles=[];for(let a=0;a<n;a++){if(seen.has(a))continue;const cycle=[];let b=a;do{seen.add(b);cycle.push(b+1);b=p[b];}while(b!==a);if(cycle.length>1)cycles.push('('+cycle.join('')+')');}return cycles.join('')||'e';});
 const g=group('S'+String(n).replace(/\d/g,d=>'₀₁₂₃₄₅₆₇₈₉'[d]),labels,(a,b)=>index.get(permutations[b].map(x=>permutations[a][x]).join(',')));
 g.seeds=[labels.indexOf('(12)'),labels.indexOf('('+Array.from({length:n},(_,i)=>i+1).join('')+')')];g.family='symmetric';return g;
}
for(const n of [4,5])groups['S'+n]=symmetric(n);
for(const n of [3,4,5,8]){const g=group('C'+'₀₁₂₃₄₅₆₇₈₉'[n],Array.from({length:n},(_,i)=>i?'r'+(i===1?'':String(i).replace(/\d/g,d=>'⁰¹²³⁴⁵⁶⁷⁸⁹'[d])):'e'),(a,b)=>(a+b)%n);g.seeds=[1];groups['C'+n]=g;}
for(const n of [3,5,6]){const g=group('D'+'₀₁₂₃₄₅₆₇₈₉'[n],Array.from({length:2*n},(_,i)=>i===0?'e':(i%n?'r'+(i%n===1?'':String(i%n).replace(/\d/g,d=>'⁰¹²³⁴⁵⁶⁷⁸⁹'[d])):'')+(i>=n?'s':'')),(a,b)=>((a%n+(a<n?1:-1)*(b%n)+n)%n)+n*((Math.floor(a/n)+Math.floor(b/n))%2));g.seeds=[1,n];groups['D'+n]=g;}
groups.V4=group('V₄',['e','a','b','ab'],(a,b)=>a^b);groups.V4.seeds=[1,2];
groups.S3.family='symmetric';groups.S3.seeds=[1,2];groups.C6.seeds=[1];groups.D4.seeds=[1,4];groups.Q8.seeds=[2,4];
export class Closure {
  constructor(g,seeds){this.g=g;this.elements=new Set(seeds);if(!this.elements.size)throw Error('SEEDS');this.round=0;this.done=false;this.count=0;this.begin();}
  begin(){this.round++;this.snapshot=[...this.elements];this.pairs=this.snapshot.flatMap(a=>this.snapshot.map(b=>[a,b]));this.cursor=0;this.added=0;}
  next(){
    if(this.done)return null;
    if(this.cursor===this.pairs.length){if(!this.added){this.done=true;return null;}this.begin();}
    const [a,b]=this.pairs[this.cursor++],c=this.g.table[a][b],fresh=!this.elements.has(c);
    if(fresh){this.elements.add(c);this.added++;}this.count++;
    return {a,b,c,fresh,round:this.round,index:this.cursor,total:this.pairs.length};
  }
}
// Equal masses: transfer the normal component; conserve tangential components.
export function collide(a,b,n){const d=(a.x-b.x)*n.x+(a.y-b.y)*n.y;return [{x:a.x-d*n.x,y:a.y-d*n.y},{x:b.x+d*n.x,y:b.y+d*n.y}];}
