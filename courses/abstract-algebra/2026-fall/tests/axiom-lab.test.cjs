const fs=require('node:fs'),vm=require('node:vm'),path=require('node:path'),assert=require('node:assert/strict');const c={window:{}};vm.runInNewContext(fs.readFileSync(path.join(__dirname,'../lesson-1/axiom-lab.js'),'utf8'),c);const M=c.window.GroupAxiomLab;let sufficient=0;
for(let mask=0;mask<32;mask++){
 const s=Object.fromEntries(M.keys.map((k,i)=>[k,!!(mask&(1<<i))])),r=M.solve(s);
 if(r.group){sufficient++;continue;}
 assert.equal(M.inspect(r.table).group,false);for(const k of M.keys)if(s[k])assert.equal(r.facts[k],true,mask+':'+k);
 if(r.table.length===3){assert(s.L&&s.R&&(s.I||s.J));for(let bits=0;bits<16;bits++){const f=M.inspect([[bits&1,(bits>>1)&1],[(bits>>2)&1,(bits>>3)&1]]);assert(f.group||M.keys.some(k=>s[k]&&!f.facts[k]));}}
}
// Exhaust every binary operation on three elements; none refutes a sufficient case.
for(let code=0;code<3**9;code++){let x=code;const table=Array.from({length:3},()=>Array.from({length:3},()=>{const v=x%3;x=Math.floor(x/3);return v;}));const r=M.inspect(table);if(M.implies(r.facts))assert(r.group);}
assert.equal(M.solve({A:true,R:true,I:true}).group,false);assert.equal(M.solve({A:true,L:true,I:true}).group,true);
console.log(`PASS: all 32 combinations; ${sufficient} sufficient sets; minimal counterexamples; all 19683 three-element operations checked.`);
