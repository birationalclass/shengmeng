const assert=require('node:assert/strict'),M=require('./models.js'),fs=require('node:fs'),vm=require('node:vm');
for(const G of [M.cyclic(6),M.cyclic(12),M.dihedral(3),M.dihedral(4)]){
 for(const a of G.elements){assert.equal(G.mul(a,G.e),a);assert.equal(G.mul(G.e,a),a);assert.equal(G.mul(a,M.inverse(G,a)),G.e);assert.equal(G.elements.length%M.order(G,a),0);for(const b of G.elements)for(const c of G.elements)assert.equal(G.mul(G.mul(a,b),c),G.mul(a,G.mul(b,c)));}
 // Exhaustive subsets: generated closure is a subgroup and the smallest one containing the seed.
 const subs=[];for(let mask=1;mask<2**G.elements.length;mask++){const H=G.elements.filter(a=>mask>>a&1);if(M.subgroup(G,H).ok)subs.push(H);}
 for(const H of subs){const blocks=M.cosets(G,H);assert.equal(blocks.length*H.length,G.elements.length);assert.equal(new Set(blocks.flat()).size,G.elements.length);assert.equal(blocks.flat().length,G.elements.length);if(M.normal(G,H))for(const A of blocks)for(const B of blocks){const target=M.coset(G,H,G.mul(A[0],B[0]));for(const a of A)for(const b of B)assert(target.includes(G.mul(a,b)));}}
 for(const a of G.elements)for(const b of G.elements){const generated=M.generated(G,[a,b]).H;assert(M.subgroup(G,generated).ok);for(const H of subs.filter(h=>h.includes(a)&&h.includes(b)))assert(generated.every(x=>H.includes(x)));}
}
const D=M.dihedral(3);assert(M.normal(D,[0,1,2]));assert(!M.normal(D,[0,3]));assert.deepEqual(M.coset(D,[0,3],1),[1,4]);assert.deepEqual(M.coset(D,[0,3],1,true),[1,5]);
for(let n=2;n<=20;n++)for(let k=0;k<n;k++)assert.equal(M.order(M.cyclic(n),k),n/M.gcd(n,k));
for(const reflect of [false,true]){const b=M.burnside(reflect);assert.equal(b.fixed.reduce((n,s)=>n+s.length,0)/b.els.length,b.orbits.length);assert.equal(b.orbits.length,6);assert.equal(b.orbits.flat().length,16);}
assert.deepEqual(M.sylow(15,3).candidates,[1]);assert.deepEqual(M.sylow(21,3).candidates,[1,7]);assert.deepEqual(M.sylow(30,3).candidates,[1,10]);assert.deepEqual(M.sylow(30,5).candidates,[1,6]);
assert.equal(M.reduceWord('abBA').word,'');assert.equal(M.reduceWord('abAB').word,'abAB');
const words=['','a','A','b','B','ab','aB','abAB','baBA','abbA'];for(const a of words)for(const b of words)for(const c of words)assert.equal(M.reduceWord(M.reduceWord(a+b).word+c).word,M.reduceWord(a+M.reduceWord(b+c).word).word);
const context={window:{}};vm.createContext(context);for(const f of ['content.js','chapter-two.js','exercises.js'])vm.runInContext(fs.readFileSync(__dirname+'/'+f,'utf8'),context);
vm.runInContext(fs.readFileSync(__dirname+'/../../../../study/spectral/vendor/katex.min.js','utf8'),context);const katex=context.katex;
let entries=0,proofs=0,exercises=0;for(const [id,book] of Object.entries(context.window.GroupCourseContent)){const ids=new Set();for(const e of book.entries){assert(!ids.has(e.id));ids.add(e.id);for(const s of [e.title,e.text])assert(s[0]&&s[1]);const lines=e.tex.split(/[,;]?\\(?:qquad|quad)\s*/);const display=lines.length>1?String.raw`\begin{gathered}`+lines.join(String.raw`\\{} `)+String.raw`\end{gathered}`:e.tex;katex.renderToString(display,{throwOnError:true,strict:'ignore'});entries++;if(e.proof)proofs++;}const qs=context.window.GroupCourseExercises[id];assert.equal(qs.length,5);for(const q of qs){assert(q.question[0]&&q.question[1]&&q.reason[0]&&q.reason[1]);if(!q.written)assert(q.answer>=0&&q.answer<q.options.length);exercises++;}}
console.log({status:'passed',newSections:12,entries,proofs,exercises});
