(function(root){
  'use strict';
  const mod=(a,n)=>((a%n)+n)%n;
  const gcd=(a,b)=>b?gcd(b,a%b):Math.abs(a);
  const range=n=>Array.from({length:n},(_,i)=>i);
  function inspectRelation(R){
    const n=R.length, failures={reflexive:null,symmetric:null,transitive:null};
    for(let a=0;a<n;a++) {
      if(!R[a][a]&&!failures.reflexive)failures.reflexive=[a];
      for(let b=0;b<n;b++){
        if(R[a][b]&&!R[b][a]&&!failures.symmetric)failures.symmetric=[a,b];
        for(let c=0;c<n;c++)if(R[a][b]&&R[b][c]&&!R[a][c]&&!failures.transitive)failures.transitive=[a,b,c];
      }
    }
    const valid=Object.values(failures).every(x=>x===null);
    const blocks=[];
    if(valid)for(let a=0;a<n;a++)if(!blocks.some(b=>b.includes(a)))blocks.push(range(n).filter(b=>R[a][b]));
    return {failures,valid,blocks};
  }
  const fromBlocks=blocks=>{const n=blocks.flat().length;return range(n).map(a=>range(n).map(b=>blocks.some(c=>c.includes(a)&&c.includes(b))));};
  const partitions3=[[[0],[1],[2]],[[0,1],[2]],[[0,2],[1]],[[0],[1,2]],[[0,1,2]]];
  const d3labels=['e','r','r²','s','rs','r²s'];
  function d3mul(a,b){const k=mod(a%3+(a<3?1:-1)*(b%3),3);return k+3*((a>=3)!==(b>=3));}
  const d3apply=(a,i)=>mod(a%3+(a<3?i:-i),3);
  function model(key){
    const common={label:x=>String(x),identity:0,opSymbol:'+',format:(a,b,c)=>`${a} + ${b} ≡ ${c} (mod 6)`};
    switch(key){
      case 'add6':return {...common,name:'(ℤ₆, +)',elements:range(6),op:(a,b)=>mod(a+b,6),note:'加法的单位元是 [0]；[a] 的逆元是 [−a]。',label:x=>`[${x}]`};
      case 'mul6':return {...common,name:'(ℤ₆, ×)',elements:range(6),op:(a,b)=>mod(a*b,6),identity:1,opSymbol:'×',format:(a,b,c)=>`${a} × ${b} ≡ ${c} (mod 6)`,note:'封闭且结合，也有单位元 [1]；但 [0]、[2]、[3]、[4] 没有乘法逆元。',label:x=>`[${x}]`};
      case 'nonzero6':return {...common,name:'(ℤ₆ ∖ {[0]}, ×)',elements:[1,2,3,4,5],op:(a,b)=>mod(a*b,6),identity:1,opSymbol:'×',format:(a,b,c)=>`${a} × ${b} ≡ ${c} (mod 6)`,note:'删掉 [0] 仍不够：[2] × [3] = [0]，结果跑出了集合。',label:x=>`[${x}]`};
      case 'unit5':return {...common,name:'(U(5), ×)',elements:[1,2,3,4],op:(a,b)=>mod(a*b,5),identity:1,opSymbol:'×',format:(a,b,c)=>`${a} × ${b} ≡ ${c} (mod 5)`,note:'这就是教材第 12 页的群表。注意 [2] 与 [3] 互为逆元。',label:x=>`[${x}]`};
      case 'unit8':return {...common,name:'(U(8), ×)',elements:[1,3,5,7],op:(a,b)=>mod(a*b,8),identity:1,opSymbol:'×',format:(a,b,c)=>`${a} × ${b} ≡ ${c} (mod 8)`,note:'四个元素都等于自己的逆元；群的阶是 4，但非单位元的阶都是 2。',label:x=>`[${x}]`};
      case 'subtract3':return {...common,name:'(ℤ₃, −)',elements:range(3),op:(a,b)=>mod(a-b,3),opSymbol:'−',format:(a,b,c)=>`${a} − ${b} ≡ ${c} (mod 3)`,note:'每格都有结果还不够。减法不结合，也没有双侧单位元。',label:x=>`[${x}]`};
      case 'd3':return {...common,name:'三角形的对称群 D₃',elements:range(6),op:d3mul,opSymbol:'∘',format:(a,b,c)=>`${d3labels[a]} ∘ ${d3labels[b]} = ${d3labels[c]}（先右后左）`,note:'由全部六种对称变换组成。它满足群公理，但不满足交换律。',label:x=>d3labels[x]};
      default:throw new Error('Unknown group example: '+key);
    }
  }
  function inspectOperation(M){
    const E=M.elements,op=M.op,closed=E.every(a=>E.every(b=>E.includes(op(a,b))));
    let closureWitness=null,associativeWitness=null,commutativeWitness=null;
    for(const a of E)for(const b of E){
      if(!E.includes(op(a,b))&&!closureWitness)closureWitness=[a,b,op(a,b)];
      if(op(a,b)!==op(b,a)&&!commutativeWitness)commutativeWitness=[a,b];
      if(closed)for(const c of E)if(op(op(a,b),c)!==op(a,op(b,c))&&!associativeWitness)associativeWitness=[a,b,c,op(op(a,b),c),op(a,op(b,c))];
    }
    const identity=E.find(e=>E.every(a=>op(e,a)===a&&op(a,e)===a));
    const inverses=E.map(a=>identity===undefined?undefined:E.find(b=>op(a,b)===identity&&op(b,a)===identity));
    return {closed,closureWitness,associative:closed?associativeWitness===null:null,associativeWitness,identity,inverses,allInverses:identity===undefined?null:inverses.every(x=>x!==undefined),commutative:!commutativeWitness,commutativeWitness,isGroup:closed&&!associativeWitness&&identity!==undefined&&inverses.every(x=>x!==undefined)};
  }
  function cycle(M,a){
    const data=inspectOperation(M);
    if(!data.isGroup)throw new Error('Element order is defined here only for groups');
    const seq=[data.identity];let x=data.identity;
    for(let k=1;k<=M.elements.length;k++){x=M.op(x,a);seq.push(x);if(x===data.identity)return seq;}
    throw new Error('Finite group order bound failed');
  }
  const api={mod,gcd,range,inspectRelation,fromBlocks,partitions3,d3labels,d3mul,d3apply,model,inspectOperation,cycle};
  if(typeof module!=='undefined'&&module.exports)module.exports=api;
  else root.AlgebraLessonMath=Object.freeze(api);
})(typeof globalThis!=='undefined'?globalThis:this);
