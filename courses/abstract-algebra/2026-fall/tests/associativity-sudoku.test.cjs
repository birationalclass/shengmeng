const assert=require('node:assert/strict');
const {initial,inspect,deduction,product,level,puzzle}=require('../lesson-1/associativity-sudoku.js');
for(let n=2;n<=9;n++){
  const v=initial(n),clues=[...v];assert.equal(v.length,n*n);assert.ok(v.includes(0));
  let count=0;
  while(v.includes(0)){
    const h=deduction(v);assert.ok(h,`Level ${n} must always offer a forced next step`);
    assert.equal(v[h.target],0);assert.equal(h.value,product(Math.floor(h.target/n)+1,h.target%n+1,n));
    if(h.latin){const known=h.cells.filter(i=>i!==h.target).map(i=>v[i]);assert.equal(new Set(known).size,n-1);assert.ok(known.every(Boolean));assert.ok(!known.includes(h.value));}
    else{const at=(a,b)=>v[(a-1)*n+b-1];assert.equal(at(h.a,h.b),h.ab);assert.equal(at(h.b,h.c),h.bc);assert.equal(v[h.target===h.left?h.right:h.left],h.value);}
    v[h.target]=h.value;assert.ok(++count<=n*n);
  }
  for(let x=1;x<=n;x++){assert.equal(v[(n-1)*n+x-1],x);assert.equal(v[(x-1)*n+n-1],x);}
  assert.equal(inspect(v).kind,'complete');assert.equal(inspect(v).checked,n**3);
  assert.equal(v.some((value,i)=>value!==v[(i%n)*n+Math.floor(i/n)]),n===6||n===8);
  const bad=[...v];bad[n*n-1]=bad[n*n-2];assert.equal(inspect(bad).kind,'repeat');
  if(n>=3)for(let i=0;i<n;i++){assert.ok(clues.slice(i*n,(i+1)*n).some(x=>!x));assert.ok(clues.some((v,j)=>j%n===i&&!v));}
  assert.equal(puzzle(n).certificate.length,count);
  console.log(`${n}×${n}: ${level(n).name}, ${clues.filter(Boolean).length} clues, ${puzzle(n).assoc} associativity deductions`);
}
const latin=Array.from({length:9},(_,i)=>(Math.floor(i/3)-i%3+3)%3+1);
assert.equal(inspect(latin).kind,'associativity');assert.equal(inspect(initial(5)).kind,'partial');
console.log('PASS: forced-step certificates, scattered blanks, non-1 identities, noncommutative levels, and all associativity checks.');
