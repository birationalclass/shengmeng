/* Small exact integer models for the classroom demos. Inputs are bounded by
   the UI; no floating-point factorization or probabilistic primality claims. */
(function(root,factory){const api=factory();if(typeof module==='object'&&module.exports)module.exports=api;else root.RingModels=api;})(typeof window!=='undefined'?window:globalThis,()=>{
'use strict';
const range=n=>Array.from({length:n},(_,i)=>i),mod=(a,n)=>((a%n)+n)%n;
function gcd(a,b){a=Math.abs(a);b=Math.abs(b);while(b)[a,b]=[b,a%b];return a;}
function egcd(a,b){let x=a,y=b,s=1,t=0,u=0,v=1;const steps=[];while(y){const q=Math.floor(x/y),r=x-q*y,rs=s-q*u,rt=t-q*v;steps.push({a:x,b:y,q,r,s:rs,t:rt});[x,y,s,t,u,v]=[y,r,u,v,rs,rt];}const sign=x<0?-1:1;return{g:sign*x,s:sign*s,t:sign*t,steps};}
const prime=n=>Number.isInteger(n)&&n>=2&&!range(Math.max(0,Math.floor(Math.sqrt(n))-1)).some(i=>n%(i+2)===0);
const divisors=n=>range(n).map(i=>i+1).filter(d=>n%d===0);
function inverse(a,n){const e=egcd(mod(a,n),n);return e.g===1?mod(e.s,n):null;}
function residues(n){return range(n).map(a=>({a,inverse:inverse(a,n),zeroWitness:a?range(n).slice(1).find(b=>mod(a*b,n)===0)??null:null}));}
const ideal=(n,d)=>range(n).filter(a=>a%gcd(n,d)===0);
function ringMap(m,n,k){k=mod(k,n);const wellDefined=mod(m*k,n)===0,multiplicative=mod(k*k-k,n)===0;return{wellDefined,multiplicative,hom:wellDefined&&multiplicative,unital:k===1,map:range(m).map(a=>mod(a*k,n)),kernel:range(m).filter(a=>mod(a*k,n)===0)};}
const trim=a=>{a=[...a];while(a.length>1&&a[a.length-1]===0)a.pop();return a.length?a:[0];};
const normalize=(a,p=0)=>trim(a.map(x=>p?mod(x,p):x));
const degree=a=>{a=trim(a);return a.length===1&&a[0]===0?null:a.length-1;};
const polyAdd=(a,b,p=0)=>normalize(range(Math.max(a.length,b.length)).map(i=>(a[i]||0)+(b[i]||0)),p);
const polyScale=(a,c,p=0)=>normalize(a.map(x=>x*c),p);
function polyMul(a,b,p=0){const c=Array(a.length+b.length-1).fill(0);a.forEach((v,i)=>b.forEach((w,j)=>c[i+j]+=v*w));return normalize(c,p);}
function polyDiv(f,g,p){if(!prime(p))throw Error('Polynomial division demo requires a prime modulus.');f=normalize(f,p);g=normalize(g,p);if(degree(g)===null)throw Error('Zero divisor polynomial.');let q=[0],r=f;const steps=[],dg=degree(g),inv=inverse(g[dg],p);while(degree(r)!==null&&degree(r)>=dg){const k=degree(r)-dg,c=mod(r.at(-1)*inv,p),term=Array(k).fill(0).concat(c),before=r;q=polyAdd(q,term,p);r=polyAdd(r,polyScale(polyMul(term,g,p),-1,p),p);steps.push({before,term,q:[...q],r:[...r]});}return{q,r,steps};}
const polyEval=(f,x,p=0)=>f.reduceRight((v,a)=>p?mod(v*x+a,p):v*x+a,0);
function quadraticRing(p,constant=1,linear=0){if(!prime(p))throw Error('Prime coefficient field required.');const pair=a=>[a%p,Math.floor(a/p)],label=a=>{const[x,y]=pair(a);return y?(x?x+' + ':'')+(y===1?'':y)+'θ':String(x);},mul=(a,b)=>{const[x,y]=pair(a),[u,v]=pair(b);return mod(x*u-constant*y*v,p)+p*mod(x*v+y*u-linear*y*v,p);};const elements=range(p*p);return{p,elements,pair,label,mul,add:(a,b)=>{const[x,y]=pair(a),[u,v]=pair(b);return mod(x+u,p)+p*mod(y+v,p);},inverse:a=>elements.find(b=>mul(a,b)===1)??null,zeroWitness:a=>a?elements.slice(1).find(b=>mul(a,b)===0)??null:null};}
const matMul=(a,b)=>[a[0]*b[0]+a[1]*b[2],a[0]*b[1]+a[1]*b[3],a[2]*b[0]+a[3]*b[2],a[2]*b[1]+a[3]*b[3]];
const quaternion=(a,b)=>[a[0]*b[0]-a[1]*b[1]-a[2]*b[2]-a[3]*b[3],a[0]*b[1]+a[1]*b[0]+a[2]*b[3]-a[3]*b[2],a[0]*b[2]-a[1]*b[3]+a[2]*b[0]+a[3]*b[1],a[0]*b[3]+a[1]*b[2]-a[2]*b[1]+a[3]*b[0]].map(x=>x||0);
const gaussianMul=(a,b)=>[a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]],norm=a=>a[0]**2+a[1]**2;
function gaussianDiv(a,b){const n=norm(b);if(!n)throw Error('Nonzero denominator required.');const numerator=gaussianMul(a,[b[0],-b[1]]),z=numerator.map(x=>x/n),q=z.map(Math.round),bq=gaussianMul(b,q),r=a.map((x,i)=>x-bq[i]);return{z,q,r,normR:norm(r),normB:n};}
const content=f=>f.reduce((g,a)=>gcd(g,a),0);
function factors(n){n=Math.abs(n);const result=[];for(let p=2;p*p<=n;p++){let e=0;while(n%p===0){e++;n/=p;}if(e)result.push([p,e]);}if(n>1)result.push([n,1]);return result;}
function fraction(a,b){if(!b)throw Error('Zero denominator.');const g=gcd(a,b),sign=b<0?-1:1;return[a/g*sign,b/g*sign];}
const fractionAdd=(a,b)=>fraction(a[0]*b[1]+b[0]*a[1],a[1]*b[1]);
const fractionMul=(a,b)=>fraction(a[0]*b[0],a[1]*b[1]);
function binomial(n){const row=[1];for(let k=1;k<=n;k++)row.push(row[k-1]*(n-k+1)/k);return row;}
return{range,mod,gcd,egcd,prime,divisors,inverse,residues,ideal,ringMap,normalize,degree,polyAdd,polyScale,polyMul,polyDiv,polyEval,quadraticRing,matMul,quaternion,gaussianMul,gaussianDiv,norm,content,factors,fraction,fractionAdd,fractionMul,binomial};
});
