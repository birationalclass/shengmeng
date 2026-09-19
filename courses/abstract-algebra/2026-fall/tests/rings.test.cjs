const assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),vm=require('node:vm');
const root=path.resolve(__dirname,'..'),M=require('../lesson-groups/ring-models.js');
let checks=0;
for(let n=2;n<=40;n++)for(const row of M.residues(n)){
 assert.equal(row.inverse!==null,M.gcd(row.a,n)===1);if(row.inverse!==null)assert.equal(M.mod(row.a*row.inverse,n),1);
 if(row.zeroWitness!==null){assert.notEqual(row.a,0);assert.notEqual(row.zeroWitness,0);assert.equal(M.mod(row.a*row.zeroWitness,n),0);}checks++;
}
for(let a=-75;a<=75;a++)for(let b=-75;b<=75;b++){
 const e=M.egcd(a,b);assert.equal(e.g,M.gcd(a,b));assert.equal(e.s*a+e.t*b,e.g);
 for(const s of e.steps){assert.equal(s.a,s.q*s.b+s.r);assert.equal(s.r,s.s*a+s.t*b);}checks++;
}
for(let m=2;m<=12;m++)for(let n=2;n<=12;n++)for(let k=0;k<n;k++){
 const map=M.ringMap(m,n,k),f=a=>M.mod(k*a,n);let direct=true;
 for(let a=0;a<m;a++)for(let b=0;b<m;b++)if(f((a+b)%m)!==M.mod(f(a)+f(b),n)||f(a*b%m)!==M.mod(f(a)*f(b),n))direct=false;
 assert.equal(map.hom,direct);checks++;
}
for(const p of [2,3,5,7]){
 for(let seed=0;seed<150;seed++){
  const f=M.range(5).map((_,i)=>M.mod(seed*(i+3)+i*i+1,p)),g=[seed%p,1+(seed%(p-1))],r=M.polyDiv(f,g,p);
  assert.deepEqual(M.polyAdd(M.polyMul(g,r.q,p),r.r,p),M.normalize(f,p));assert(M.degree(r.r)===null||M.degree(r.r)<M.degree(M.normalize(g,p)));checks++;
 }
 const Q=M.quadraticRing(p);
 for(const a of Q.elements){assert.equal(Q.mul(a,1),a);const inv=Q.inverse(a);if(inv!==null)assert.equal(Q.mul(a,inv),1);
  for(const b of Q.elements)for(const c of Q.elements){assert.equal(Q.mul(Q.mul(a,b),c),Q.mul(a,Q.mul(b,c)));assert.equal(Q.mul(a,Q.add(b,c)),Q.add(Q.mul(a,b),Q.mul(a,c)));}checks++;
 }
}
assert(M.quadraticRing(3).elements.slice(1).every(a=>M.quadraticRing(3).inverse(a)!==null));
assert.equal(M.quadraticRing(2).mul(3,3),0);
for(let a=-4;a<=4;a++)for(let b=-4;b<=4;b++)for(let c=-3;c<=3;c++)for(let d=-3;d<=3;d++){
 if(c===0&&d===0)continue;const x=[a,b],y=[c,d],r=M.gaussianDiv(x,y),product=M.gaussianMul(y,r.q);assert.deepEqual(product.map((v,i)=>v+r.r[i]),x);assert(r.normR<r.normB);assert.equal(M.norm(M.gaussianMul(x,y)),M.norm(x)*M.norm(y));checks++;
}
const basis=M.range(4).map(i=>M.range(4).map(j=>i===j?1:0));for(const a of basis)for(const b of basis)for(const c of basis)assert.deepEqual(M.quaternion(M.quaternion(a,b),c),M.quaternion(a,M.quaternion(b,c)));
assert.deepEqual(M.quaternion([1,-2,1,3],[2,1,4,-2]),[6,-17,5,-5]);
for(let seed=1;seed<500;seed++){const f=[seed%5-2,seed%7-3,seed%11-5],g=[seed%3-1,seed%13-6];assert.equal(M.content(M.polyMul(f,g)),M.content(f)*M.content(g));checks++;}
assert.deepEqual(M.fractionAdd([2,3],[1,6]),[5,6]);assert.deepEqual(M.fractionMul([-2,3],[3,-5]),[2,5]);
const context=vm.createContext({window:{}});for(const file of ['content.js','chapter-two.js','exercises.js','textbook-references.js','chapter-three.js','chapter-four.js','ring-exercises.js','math-format.js'])vm.runInContext(fs.readFileSync(path.join(root,'lesson-groups',file),'utf8'),context,{filename:file});
vm.runInContext(fs.readFileSync(path.join(root,'../../../study/spectral/vendor/katex.min.js'),'utf8'),context);
context.window.katex=context.katex;
let cards=0,proofs=0,questions=0;const seen=new Set();
function prose(value){if(Array.isArray(value))value.forEach(prose);else if(typeof value==='string'){const html=context.window.GroupLessonMath.inline(value);assert(!html.includes('katex-error'));}}
for(const [id,book] of Object.entries(context.window.GroupCourseContent).filter(([id])=>+id[0]>=3)){
 const ids=new Set();for(const e of book.entries){assert(!ids.has(e.id));ids.add(e.id);assert(e.title[0]&&e.title[1]&&e.text[0]&&e.text[1]);
  const ref=context.window.GroupTextbookReferences[id][e.id];assert(ref.pdfPages.every(p=>p>=136&&p<=226));assert(!/[\u4e00-\u9fff]/.test(ref.label[1]),ref.label[1]);
  for(const m of ref.label[0].matchAll(/(?:定义|定理)\s+(\d\.\d\.\d+)/g))seen.add(m[0].replace(/\s+/g,''));
  const lines=e.tex.split(/[,;]?\\(?:qquad|quad)\s*/);context.katex.renderToString(lines.length>1?String.raw`\begin{gathered}`+lines.join(String.raw`\\{} `)+String.raw`\end{gathered}`:e.tex,{throwOnError:true,strict:'ignore'});
  for(const key of ['text','proof','example','warning','extraProof'])prose(e[key]);cards++;if(e.proof)proofs++;
 }
 const qs=context.window.GroupCourseExercises[id];assert.equal(qs.length,5);assert(qs.at(-1).written);for(const q of qs){prose(q.question);prose(q.reason);assert(q.question.every(Boolean)&&q.reason.every(Boolean));if(!q.written){assert.equal(q.options.length,4);assert(q.answer>=0&&q.answer<4);assert.equal(new Set(q.options.map(x=>JSON.stringify(x))).size,4);}questions++;}
}
// Every numbered definition/theorem in these textbook sections is represented.
const counts={'3.1':[2,3],'3.2':[5,1],'3.3':[3,4],'3.4':[2,5],'3.5':[2,3],'3.6':[2,5],'4.1':[3,3],'4.2':[1,2],'4.3':[10,9],'4.4':[2,6],'4.5':[1,6]};
for(const[id,[defs,thms]]of Object.entries(counts))for(const[type,n]of [['定义',defs],['定理',thms]])for(let i=1;i<=n;i++)assert(seen.has(type+id+'.'+i),'Missing textbook '+type+id+'.'+i);
assert.equal(cards,84);assert.equal(questions,55);
console.log({status:'PASS',modelCases:checks,sections:11,cards,proofs,questions,textbookCoverage:'all numbered definitions and theorems'});
