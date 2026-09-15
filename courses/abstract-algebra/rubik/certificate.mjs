import {FACES,MOVES,mobilePermutation,identity,compose,inverse} from './cube-core.mjs';
export function factorial(n){let v=1n;for(let i=2n;i<=BigInt(n);i++)v*=i;return v;}
export const STATE_BOUND=factorial(8)*factorial(12)*3n**7n*2n**11n/2n;
const assert=(condition,message)=>{if(!condition)throw Error(message);};
// This checker establishes a lower bound, not the completeness of a BSGS.
// Each generator is a certified word in face turns fixing earlier base points.
// Hence its computed orbit is a subset of the actual stabilizer's orbit.
export function verifyCertificate(cert){
  assert(cert.format==='rubik-orbit-lower-bound-v1'&&cert.degree===48&&cert.convention==='left-to-right','证书格式不符');
  assert(cert.nodes.length<10000&&cert.levels.length<=48,'证书超出合理长度');
  const values=[];
  const get=i=>{assert(Number.isInteger(i)&&i>=0&&i<values.length,'引用必须指向先前的节点');return values[i];};
  for(const node of cert.nodes){
    let p;if(node[0]==='move'){assert(FACES.includes(node[1]),'未知生成元');p=mobilePermutation(MOVES[node[1]]);}
    else if(node[0]==='inverse')p=inverse(get(node[1]));
    else if(node[0]==='word'){assert(Array.isArray(node[1])&&node[1].length<10000,'词过长');p=node[1].reduce((a,i)=>compose(a,get(i)),identity(48));}
    else throw Error('未知证书运算');
    assert(p.length===48&&new Set(p).size===48&&p.every(i=>Number.isInteger(i)&&i>=0&&i<48),'不是置换');values.push(p);
  }
  let lowerBound=1n;const base=[],orbits=[];
  for(const level of cert.levels){
    const b=level.point;assert(Number.isInteger(b)&&b>=0&&b<48&&!base.includes(b),'基点不合法');
    const generators=level.generators.map(get);
    for(const g of generators)assert(base.every(x=>g[x]===x),'生成元没有固定先前的基点');
    const orbit=new Set([b]),queue=[b];
    for(let i=0;i<queue.length;i++)for(const g of generators){const y=g[queue[i]];if(!orbit.has(y)){orbit.add(y);queue.push(y);}}
    assert(orbit.size===level.orbitSize,'轨道大小与证书不符');lowerBound*=BigInt(orbit.size);base.push(b);orbits.push([...orbit].sort((a,b)=>a-b));
  }
  assert(lowerBound===STATE_BOUND,'轨道下界尚未达到由不变量得到的上界');
  return {lowerBound,upperBound:STATE_BOUND,nodes:values.length,base,orbits};
}
