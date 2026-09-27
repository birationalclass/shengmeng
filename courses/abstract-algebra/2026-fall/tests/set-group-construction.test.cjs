const test=require('node:test'),assert=require('node:assert/strict');
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm');
const root=path.resolve(__dirname,'..');
// Load the browser UMD bundle independently of the vendor directory's ESM scope.
const context={};context.self=context;
vm.runInNewContext(fs.readFileSync(path.resolve(root,'../../../study/spectral/vendor/katex.min.js'),'utf8'),context);
const katex=context.katex;
const data=JSON.parse(fs.readFileSync(path.join(root,'lesson-groups/sections/1.4.json')));
const entries=data.book.entries,e=entries.find(e=>e.id==='set-group-construction');
test('one original extension immediately follows Theorem 1.4.3',()=>{
 assert.equal(entries.filter(e=>e.extension).length,1);
 assert.equal(entries[entries.indexOf(e)-1].id,'cayley');
 assert.equal(entries[entries.indexOf(e)+1].id,'automorphism');
 assert.deepEqual(data.references[e.id].pdfPages,[]);
 assert.match(e.text[0],/选择公理/);
 assert.equal(e.tex,'');assert.equal(e.statementOnly,true);
 assert.doesNotMatch(e.text[0],/主线|点击|f\(/);
});
test('all extension text is bilingual and every formula parses',()=>{
 const disclosures=[...e.extension.steps.flatMap(s=>s.checks),...e.extension.facts];
 assert.equal(new Set(disclosures.map(d=>d.id)).size,disclosures.length);
 let formulas=0;
 function visit(node){
  if(!node||typeof node!=='object')return;
  for(const key of ['title','text'])if(key in node){assert.equal(node[key].length,2);node[key].forEach(t=>assert(t.length>0));}
  if(node.tex){katex.renderToString(node.tex,{throwOnError:true,strict:'error'});formulas++;}
  Object.values(node).forEach(visit);
 }
 visit(e.extension);assert(formulas>=25);
});
test('finite models satisfy the stated axioms',()=>{
 for(const n of [1,2,3,4,9])for(let a=0;a<n;a++){
  const mul=(a,b)=>(a+b)%n;
  assert.equal(mul(a,0),a);assert.equal(mul(0,a),a);assert.equal(mul(a,(n-a)%n),0);
  for(let b=0;b<n;b++)for(let c=0;c<n;c++)assert.equal(mul(mul(a,b),c),mul(a,mul(b,c)));
 }
 for(let a=0;a<32;a++)for(let b=0;b<32;b++)for(let c=0;c<32;c++){
  assert.equal((a^b)^c,a^(b^c));assert.equal(a^a,0);assert.equal(a^b,b^a);
 }
 assert.equal(3^5,6);
});
