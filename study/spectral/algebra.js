// Exact rational linear algebra. Columns represent cochains in the named total basis.
export class Q {
  constructor(n=0n,d=1n){n=BigInt(n);d=BigInt(d);if(!d)throw Error('Zero denominator');if(d<0n){n=-n;d=-d;}let a=n<0n?-n:n,b=d;while(b){[a,b]=[b,a%b];}this.n=n/(a||1n);this.d=d/(a||1n);}
  add(b){b=q(b);return new Q(this.n*b.d+b.n*this.d,this.d*b.d);}
  neg(){return new Q(-this.n,this.d);} sub(b){return this.add(q(b).neg());}
  mul(b){b=q(b);return new Q(this.n*b.n,this.d*b.d);} div(b){b=q(b);return new Q(this.n*b.d,this.d*b.n);}
  get zero(){return this.n===0n;} toString(){return this.d===1n?`${this.n}`:`${this.n}/${this.d}`;}
}
export const q=x=>x instanceof Q?x:new Q(x);
const zeros=n=>Array.from({length:n},()=>q(0));
export const basisVector=(n,i)=>zeros(n).map((x,j)=>q(i===j?1:0));
export function rref(A,ncols=A[0]?.length||0){A=A.map(row=>row.map(q));let r=0,pivots=[];for(let c=0;c<ncols&&r<A.length;c++){let i=A.findIndex((row,k)=>k>=r&&!row[c].zero);if(i<0)continue;[A[i],A[r]]=[A[r],A[i]];let v=A[r][c];A[r]=A[r].map(x=>x.div(v));for(let j=0;j<A.length;j++)if(j!==r){v=A[j][c];A[j]=A[j].map((x,k)=>x.sub(v.mul(A[r][k])));}pivots.push(c);r++;}return {A,pivots};}
export function kernel(A,ncols=A[0]?.length||0){let {A:R,pivots}=rref(A,ncols),out=[];for(let j=0;j<ncols;j++)if(!pivots.includes(j)){let v=basisVector(ncols,j);pivots.forEach((p,i)=>v[p]=R[i][j].neg());out.push(v);}return out;}
const rows=(cols,n)=>Array.from({length:n},(_,i)=>cols.map(c=>c[i]));
export const rank=(cols,n)=>rref(rows(cols,n),cols.length).pivots.length;
export const independent=(cols,n)=>{const ps=rref(rows(cols,n),cols.length).pivots;return ps.map(i=>cols[i]);};
export const combine=(cols,cs,n)=>cols.reduce((v,c,i)=>v.map((x,j)=>x.add(c[j].mul(cs[i]))),zeros(n));
export function coordinates(cols,v){let {A,pivots}=rref(rows([...cols,v],v.length),cols.length);for(let row of A)if(row.slice(0,cols.length).every(x=>x.zero)&&!row.at(-1).zero)throw Error('Vector outside span');let out=zeros(cols.length);pivots.forEach((p,i)=>out[p]=A[i].at(-1));return out;}
const g=(id,p,q)=>({id,p,q});
export const examples={
  d2:{name:'非零 d₂',description:'四个一维空间；d₁ = 0，但 d₂ 是同构。',gens:[g('b',0,1),g('c',1,0),g('u',1,1),g('z',2,0)],h:[['b','u',1],['c','z',1]],v:[['c','u',-1]]},
  survive:{name:'有存活类的例子',description:'在 d₂ 例子上直和三个零微分生成元；可对照非零的稳定页与总上同调。',gens:[g('a',0,0),g('e',1,0),g('t',0,2),g('b',0,1),g('c',1,0),g('u',1,1),g('z',2,0)],h:[['b','u',1],['c','z',1]],v:[['c','u',-1]]},
  d3:{name:'非零 d₃',description:'两次修正后出现第三微分；d₁、d₂ 均为零仍不代表退化。',gens:[g('b',0,2),g('c',1,1),g('e',2,0),g('u',1,2),g('v',2,1),g('z',3,0)],h:[['b','u',1],['c','v',1],['e','z',1]],v:[['c','u',-1],['e','v',-1]]}
};
export class Complex {
 constructor(ex){this.ex=ex;this.maxP=Math.max(...ex.gens.map(g=>g.p));this.maxQ=Math.max(...ex.gens.map(g=>g.q));this.maxN=Math.max(...ex.gens.map(g=>g.p+g.q));this.cache=new Map();this.validate();}
 basis(n){return this.ex.gens.filter(g=>g.p+g.q===n);}
 apply(a,n,kind='D'){const source=this.basis(n),target=this.basis(n+1);let out=zeros(target.length);const edges=kind==='D'?[...this.ex.h,...this.ex.v]:this.ex[kind];for(let [s,t,c]of edges){let i=source.findIndex(g=>g.id===s),j=target.findIndex(g=>g.id===t);if(i>=0&&j>=0)out[j]=out[j].add(a[i].mul(c));}return out;}
 filtered(n,p){return this.basis(n).flatMap((g,i)=>g.p>=p?[basisVector(this.basis(n).length,i)]:[]);}
 cycles(n,p,r){const F=this.filtered(n,p),target=this.basis(n+1),images=F.map(v=>this.apply(v,n));const constraints=target.flatMap((g,i)=>g.p<p+r?[images.map(v=>v[i])]:[]);return kernel(constraints,F.length).map(c=>combine(F,c,this.basis(n).length));}
 boundaries(n,p,r){const F=this.filtered(n-1,p-r),images=F.map(v=>this.apply(v,n-1)),target=this.basis(n);const constraints=target.flatMap((g,i)=>g.p<p?[images.map(v=>v[i])]:[]);return independent(kernel(constraints,F.length).map(c=>combine(images,c,target.length)),target.length);}
 page(r,p,qv){const key=`${r}/${p}/${qv}`;if(this.cache.has(key))return this.cache.get(key);const n=p+qv,N=this.basis(n).length;let Z=r===0?this.filtered(n,p):this.cycles(n,p,r),den=r===0?this.filtered(n,p+1):[...this.cycles(n,p+1,r-1),...this.boundaries(n,p,r-1)];den=independent(den,N);let span=[...den],reps=[];for(let z of Z)if(rank([...span,z],N)>span.length){span.push(z);reps.push(z);}const page={r,p,q:qv,n,Z,den,reps,dim:reps.length};this.cache.set(key,page);return page;}
 differential(r,p,qv){let src=this.page(r,p,qv),tar=this.page(r,p+r,qv-r+1);return src.reps.map(v=>coordinates([...tar.den,...tar.reps],this.apply(v,src.n)).slice(tar.den.length));}
 cohomology(n){let N=this.basis(n).length,Dcols=this.filtered(n,0).map(v=>this.apply(v,n)),ker=kernel(rows(Dcols,this.basis(n+1).length),N),bd=independent(this.filtered(n-1,0).map(v=>this.apply(v,n-1)),N);return {dim:ker.length-bd.length,cycles:ker,boundaries:bd};}
 filtration(n,p){let Z=this.cycles(n,p,this.maxP+2),bd=this.cohomology(n).boundaries;return rank([...bd,...Z],this.basis(n).length)-bd.length;}
 validate(){const ids=new Set(this.ex.gens.map(g=>g.id));if(ids.size!==this.ex.gens.length)throw Error('Duplicate generator');for(let kind of ['h','v'])for(let [a,b]of this.ex[kind]){let x=this.ex.gens.find(g=>g.id===a),y=this.ex.gens.find(g=>g.id===b);if(!x||!y||y.p-x.p!==(kind==='h'?1:0)||y.q-x.q!==(kind==='v'?1:0))throw Error('Wrong bidegree');}
 for(let n=0;n<=this.maxN;n++)for(let a of this.filtered(n,0)){let h=this.apply(a,n,'h'),v=this.apply(a,n,'v');if(this.apply(h,n+1,'h').some(x=>!x.zero)||this.apply(v,n+1,'v').some(x=>!x.zero)||this.apply(h,n+1,'v').some((x,i)=>!x.add(this.apply(v,n+1,'h')[i]).zero))throw Error('Not a double complex');}}
}
export function texVector(v,base){let terms=[];v.forEach((a,i)=>{if(a.zero)return;let negative=a.n<0n,abs=negative?a.neg():a;let coefficient=abs.toString()==='1'?'':(abs.d===1n?`${abs.n}`:`\\frac{${abs.n}}{${abs.d}}`);terms.push(`${terms.length?(negative?'-':'+'):(negative?'-':'')}${coefficient}${base[i].id}`);});return terms.join('')||'0';}
export function matrixTex(cols,nrows){if(!cols.length||!nrows)return `0_{${nrows}\\times ${cols.length}}`;return `\\begin{pmatrix}${rows(cols,nrows).map(r=>r.map(x=>x.d===1n?`${x.n}`:`\\frac{${x.n}}{${x.d}}`).join('&')).join('\\\\')}\\end{pmatrix}`;}
