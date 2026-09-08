import assert from 'node:assert/strict';
import {Complex,examples,rank,combine,basisVector,Q,kernel} from './algebra.js';
let checks=0;
for(const [name,ex]of Object.entries(examples)){
 const c=new Complex(ex),R=c.maxP+2;
 for(let r=0;r<R;r++)for(let p=0;p<=c.maxP;p++)for(let q=0;q<=c.maxQ;q++){
  const E=c.page(r,p,q),T=c.page(r,p+r,q-r+1),U=c.page(r,p+2*r,q-2*r+2),M=c.differential(r,p,q),N=c.differential(r,p+r,q-r+1),I=c.differential(r,p-r,q+r-1);
  for(let col of M)assert(combine(N,col,U.dim).every(x=>x.zero),`${name} d${r}²`);
  assert.equal(E.dim-rank(M,T.dim)-rank(I,E.dim),c.page(r+1,p,q).dim,`${name} E${r+1} (${p},${q})`);checks++;
 }
 for(let n=0;n<=c.maxN;n++){let sum=0;for(let p=0;p<=n;p++){let dim=c.page(R,p,n-p).dim;sum+=dim;assert.equal(dim,c.filtration(n,p)-c.filtration(n,p+1));checks++;}assert.equal(sum,c.cohomology(n).dim);}
 // Independent expectations for the explicit examples.
 if(name==='survive')assert.deepEqual([0,1,2].map(n=>c.cohomology(n).dim),[1,1,1]);
 else assert([0,1,2,3].every(n=>c.cohomology(n).dim===0));
 if(name==='d2')assert.equal(c.differential(2,0,1)[0][0].toString(),'1');
 if(name==='d3'){assert.equal(c.page(2,0,2).dim,1);assert.equal(c.differential(3,0,2)[0][0].toString(),'1');}
 // Negative-index terms vanish without discarding their ambient complexes artificially.
 for(let r=0;r<=R;r++){assert.equal(c.page(r,-1,2).dim,0);assert.equal(c.page(r,2,-1).dim,0);}
}
assert.equal(new Q(1,3).add(new Q(1,6)).toString(),'1/2');
console.log(`PASS: ${checks} page/convergence checks; explicit d2 and d3 matrices; exact total cohomology; negative indices.`);
