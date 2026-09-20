export const DURATION=114;
export const clamp=(x,a=0,b=1)=>Math.min(b,Math.max(a,x));
export const smooth=x=>{x=clamp(x);return x*x*(3-2*x);};
export const mix=(a,b,t)=>a+(b-a)*t;
export const PHASES=[
 {id:'prologue',start:0,end:8,en:'The Grammar of Becoming',zh:'运算，生成万象',era:'A MECHANICAL ATLAS OF HUMAN IDEAS',line:'从符号到世界，从法则到智能。',sub:'A world unfolds, one operation at a time.',formula:'COMPOSE · ACT · TRANSFORM',focus:0},
 {id:'semigroup',start:8,end:38,en:'Semigroup',zh:'半群',era:'约前 1300 年 — 公元 7 世纪 · 文字的两条路径',line:'有限的符号，连接成无限的表达。',sub:'A finite alphabet. An unbounded world of words.',formula:'(uv)w = u(vw)',focus:-22},
 {id:'action',start:38,end:70,en:'Action',zh:'作用',era:'1666 — 1687 · 从苹果到运动的法则',line:'法则不只描述世界，它让状态随时间展开。',sub:'A law carries one state into the next.',formula:'Φₛ ∘ Φₜ = Φₛ₊ₜ',focus:0},
 {id:'composition',start:70,end:103,en:'Composition',zh:'复合',era:'1956 — 2017 — 今日 · 从计算到生成',line:'一层变换接续另一层，简单规则构成复杂表达。',sub:'Layer upon layer, transformations become expression.',formula:'F = fₗ ∘ ··· ∘ f₂ ∘ f₁',focus:22},
 {id:'epilogue',start:103,end:114,en:'Operations Make Worlds',zh:'运算构造世界',era:'SEMIGROUP · ACTION · COMPOSITION',line:'群刻画可逆的对称；更广义的运算，组织生成的秩序。',sub:'Composition gives structure. Symmetry reveals a group.',formula:'g · (h · x) = (gh) · x',focus:0}
];
export function phaseAt(t){return PHASES.find(p=>t>=p.start&&t<p.end)||PHASES[t<0?0:PHASES.length-1];}
// Constant-gravity flow on all of phase space R²; no impact or ground boundary.
export function gravityFlow([y,v],t,g=9.81){return [y+v*t-g*t*t/2,v-g*t];}
export const concatenate=(u,v)=>u+v;
export const compose=(f,g)=>x=>f(g(x));
export function cameraAt(t,aspect=1.78){
 const keys=[
  [0,[0,29,48],[0,1,0]], [7,[-9,21,31],[-15,1,0]],
  [13,[-10,12,18],[-22,2,0]], [25,[-15,10,17],[-22,2,0]], [34,[-28,11,18],[-22,2,0]],
  [43,[12,13,19],[0,2,0]], [53,[10,10.5,16],[0,3,0]], [64,[-8,11,17],[0,2.5,0]],
  [77,[34,13,19],[22,3,0]], [89,[29,10.5,18],[22,3,0]], [99,[17,14,21],[22,3,0]],
  [110,[0,28,47],[0,2,0]], [114,[0,30,50],[0,2,0]]
 ];
 let i=0;while(i<keys.length-2&&t>keys[i+1][0])i++;
 const a=keys[i],b=keys[i+1],u=smooth((t-a[0])/(b[0]-a[0])),pos=a[1].map((v,j)=>mix(v,b[1][j],u)),target=a[2].map((v,j)=>mix(v,b[2][j],u));
 const widen=aspect<1?2.05:1;return {pos:pos.map((v,j)=>target[j]+(v-target[j])*widen),target};
}
