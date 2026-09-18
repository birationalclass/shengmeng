/* Exact finite models. No visual position is used as mathematical evidence. */
((root)=>{
const mod=(x,n)=>(x%n+n)%n,range=n=>Array.from({length:n},(_,i)=>i),gcd=(a,b)=>b?gcd(b,a%b):Math.abs(a),lcm=(a,b)=>a/gcd(a,b)*b;
function cyclic(n){return {name:`ℤ${n}`,symbol:'+',elements:range(n),e:0,mul:(a,b)=>mod(a+b,n),label:a=>String(a),n};}
function dihedral(n){return {name:`D${n}`,symbol:'·',elements:range(2*n),e:0,n,mul:(a,b)=>mod(a%n+(a<n?1:-1)*(b%n),n)+n*((a>=n)!==(b>=n)),label:a=>a===0?'e':(a%n===0?'':a%n===1?'r':`r${sup(a%n)}`)+(a>=n?'s':''),act:(g,x)=>mod(g%n+(g<n?x:-x),n)};}
const sup=n=>String(n).replace(/[0-9]/g,x=>'⁰¹²³⁴⁵⁶⁷⁸⁹'[x]);
const inverse=(G,a)=>G.elements.find(b=>G.mul(a,b)===G.e&&G.mul(b,a)===G.e);
const equal=(a,b)=>a.length===b.length&&a.every(x=>b.includes(x));
function order(G,a){let x=G.e;for(let k=1;k<=G.elements.length;k++){x=G.mul(x,a);if(x===G.e)return k;}throw Error('Not a finite group');}
function subgroup(G,H){if(!H.length)return {ok:false,empty:true};for(const a of H)for(const b of H){const c=G.mul(a,inverse(G,b));if(!H.includes(c))return {ok:false,witness:[a,b,c]};}return {ok:true};}
function generated(G,S){let H=[...new Set([G.e,...S])],layers=[H.slice()];while(true){const next=new Set(H);for(const a of H)for(const b of H)next.add(G.mul(a,inverse(G,b)));if(next.size===H.length)break;H=[...next];layers.push(H.slice());}return {H:H.sort((a,b)=>a-b),layers};}
const coset=(G,H,g,right=false)=>H.map(h=>right?G.mul(h,g):G.mul(g,h)).sort((a,b)=>a-b);
function cosets(G,H,right=false){const blocks=[];for(const g of G.elements)if(!blocks.some(b=>b.includes(g)))blocks.push(coset(G,H,g,right));return blocks;}
const conjugate=(G,g,x)=>G.mul(G.mul(g,x),inverse(G,g));
const normal=(G,H)=>subgroup(G,H).ok&&G.elements.every(g=>equal(coset(G,H,g),coset(G,H,g,true)));
const divisors=n=>range(n).map(i=>i+1).filter(d=>n%d===0);
const primes=n=>divisors(n).filter(p=>p>1&&divisors(p).length===2);
function sylow(n,p){if(!primes(n).includes(p))throw Error('p must be a prime divisor');let m=n,a=0;while(m%p===0){m/=p;a++;}return {n,p,a,m,size:p**a,candidates:divisors(m).filter(d=>d%p===1)};}
const compose=(a,b)=>b.map(x=>a[x]);
function cycles(p){const done=new Set(),out=[];for(let i=0;i<p.length;i++)if(!done.has(i)){const c=[];let j=i;while(!done.has(j)){done.add(j);c.push(j);j=p[j];}out.push(c);}return out;}
const cycleLabel=(p,all=false)=>cycles(p).filter(c=>all||c.length>1).map(c=>'('+c.map(x=>x+1).join(' ')+')').join('')||'e';
function burnside(reflections=true){const G=dihedral(4),els=reflections?G.elements:range(4);const act=(g,mask)=>range(4).reduce((out,i)=>out|((mask>>i&1)<<G.act(g,i)),0);const fixed=els.map(g=>range(16).filter(m=>act(g,m)===m));const orbits=[];for(let m=0;m<16;m++)if(!orbits.some(o=>o.includes(m)))orbits.push([...new Set(els.map(g=>act(g,m)))].sort((a,b)=>a-b));return {G,els,act,fixed,orbits};}
const invLetter=x=>x===x.toUpperCase()?x.toLowerCase():x.toUpperCase();
function reduceWord(word){const stack=[],steps=[];for(const x of word){const cancel=stack.at(-1)===invLetter(x);if(cancel)stack.pop();else stack.push(x);steps.push({letter:x,cancel,word:stack.join('')});}return {word:stack.join(''),steps};}
const api={mod,range,gcd,lcm,cyclic,dihedral,inverse,equal,order,subgroup,generated,coset,cosets,conjugate,normal,divisors,primes,sylow,compose,cycles,cycleLabel,burnside,reduceWord,invLetter};
if(typeof module!=='undefined'&&module.exports)module.exports=api;else root.GroupModels=api;
})(globalThis);
