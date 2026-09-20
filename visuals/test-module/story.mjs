export const DURATION=208;
export const clamp=(x,a=0,b=1)=>Math.min(b,Math.max(a,x));
export const smooth=x=>{x=clamp(x);return x*x*(3-2*x);};
export const mix=(a,b,t)=>a+(b-a)*t;
export const SITES=[[-28,0,-12],[-21,0,12],[0,0,23],[22,0,9],[34,0,-15],[8,0,-38]].map(([x,y,z])=>[x*1.4,y,z*1.4]);
export const PHASES=[
 {id:'prologue',start:0,end:12,en:'The Grammar of Becoming',zh:'运算，生成万象',era:'A CLOCKWORK HISTORY OF HUMAN IDEAS',line:'一个运算，开启一个世界。',sub:'One operation sets a world in motion.',formula:'COMPOSE · ACT · TRANSFORM'},
 {id:'semigroup',start:12,end:40,en:'Semigroup',zh:'半群',era:'约前 1300 年 — 公元 7 世纪 · 文字',line:'符号连接，语言生长。',sub:'From signs to words, through concatenation.',formula:'(uv)w = u(vw)'},
 {id:'remainder',start:40,end:70,en:'Chinese Remainder Theorem',zh:'中国剩余定理',era:'1247 · 秦九韶《数书九章》',line:'不同的余数，搭起同一个整数。',sub:'Many local conditions. One coherent whole.',formula:'x ≡ 2 (3), 3 (5), 2 (7) ⇒ x ≡ 23 (105)'},
 {id:'action',start:70,end:100,en:'Action',zh:'作用',era:'1666 — 1687 · 牛顿',line:'时间推进，法则驱动状态。',sub:'Time acts. A world unfolds.',formula:'Φₛ ∘ Φₜ = Φₛ₊ₜ'},
 {id:'permutation',start:100,end:130,en:'Permutation',zh:'置换',era:'1830 年代 · 伽罗瓦',line:'根的位置改变，代数关系仍在。',sub:'Permute the roots. Preserve their relations.',formula:'Gal(x³ − 2 / ℚ) ≅ S₃'},
 {id:'symmetry',start:130,end:160,en:'Symmetry',zh:'对称',era:'1890 年代 · 晶体与空间群',line:'一个晶胞，铺展有序的空间。',sub:'A unit cell. An ordered world.',formula:'Tₐ ∘ Tᵦ = Tₐ₊ᵦ'},
 {id:'composition',start:160,end:192,en:'Composition',zh:'复合',era:'1956 — 2017 — 今日 · 人工智能',line:'层层变换，生成新的表达。',sub:'Transformation follows transformation.',formula:'F = fₗ ∘ ··· ∘ f₂ ∘ f₁'},
 {id:'epilogue',start:192,end:208,en:'Operations Make Worlds',zh:'运算构造世界',era:'SIX AGES · ONE LANGUAGE OF STRUCTURE',line:'从生成的运算，到可逆的对称。',sub:'Operations generate. Groups reveal symmetry.',formula:'g · (h · x) = (gh) · x'}
];
export function phaseAt(t){return PHASES.find(p=>t>=p.start&&t<p.end)||PHASES[t<0?0:PHASES.length-1];}
// Constant-gravity flow on all of phase space R²; no impact or ground boundary.
export function gravityFlow([y,v],t,g=9.81){return [y+v*t-g*t*t/2,v-g*t];}
export const concatenate=(u,v)=>u+v;
export const compose=(f,g)=>x=>f(g(x));

// Cubic Hermite interpolation with time-scaled tangents: a continuously moving
// cinematic crane, without coming to rest at every intermediate keyframe.
const ORIGINAL_CAMERA_KEYS=[
 [0,[-30,15,-13],[-35,12,-21]], [6,[-32,17,-9],[-35,12,-21]],
 [11,[-37,26,8],[-28,1,-12]], [18,[-17,14,6],[-28,1.8,-12]],
 [29,[-34,10,7],[-28,1.6,-12]], [35,[-39,13,1],[-28,1.8,-12]],
 [40,[-31,12,4],[-23,1.2,0]], [47,[-9,14,30],[-21,3.5,12]],
 [57,[-25,10.5,32],[-21,2.8,12]], [64,[-34,18,24],[-21,4,12]],
 [69,[-10,8,24],[-10,1,18]], [75,[13,22,39],[0,3.2,23]],
 [85,[6,12.5,44],[0,3.4,23]], [94,[-10,19,40],[0,3.2,23]],
 [100,[12,16,31],[22,2,9]], [108,[35,13,26],[22,2.5,9]],
 [118,[24,10,29],[22,2.7,9]], [126,[9,18,24],[22,2.4,9]],
 [132,[20,23,2],[34,3,-15]], [141,[47,15,2],[34,3,-15]],
 [151,[37,11,5],[34,3.2,-15]], [158,[24,21,-1],[34,3,-15]],
 [163,[23,24,-21],[8,3,-38]], [172,[23,14,-22],[8,3.4,-38]],
 [182,[2,11,-18],[8,3.2,-38]], [189,[-5,24,-24],[8,3,-38]],
 [199,[-17,60,57],[0,0,-6]], [208,[-5,77,67],[0,0,-6]]
];
export const CAMERA_KEYS=ORIGINAL_CAMERA_KEYS.map(([time,pos,target])=>{
 if(time<=6)return [time,pos,target];
 if(time===199)return [time,[-24,62,43],[0,0,-8.4]];if(time===208)return [time,[-7,77,75],[0,0,-8.4]];
 const delta=[target[0]*.4,0,target[2]*.4];return [time,pos.map((v,i)=>v+delta[i]),target.map((v,i)=>v+delta[i])];
});
export function cameraAt(t,aspect=1.78){
 if(t>DURATION){const q=t-DURATION,u=smooth(q/26),angle=Math.atan2(-7,83.4)+(q-8*(1-Math.exp(-q/8)))*.016,r=Math.hypot(-7,83.4)-u*19,target=[0,0,-8.4],height=77-u*22+Math.sin(q*.027)*4*u,widen=aspect<1?1.75:1;return {pos:[target[0]+r*Math.sin(angle)*widen,height*widen,target[2]+r*Math.cos(angle)*widen],target,roll:Math.sin(DURATION*.045)*.025*(1-u)};}
 const keys=CAMERA_KEYS; t=clamp(t,0,DURATION);let i=0;while(i<keys.length-2&&t>keys[i+1][0])i++;
 const a=keys[i],b=keys[i+1],prev=keys[Math.max(0,i-1)],next=keys[Math.min(keys.length-1,i+2)],dt=b[0]-a[0],u=(t-a[0])/dt;
 const h00=2*u**3-3*u*u+1,h10=u**3-2*u*u+u,h01=-2*u**3+3*u*u,h11=u**3-u*u;
 const interp=k=>a[k].map((x,j)=>h00*x+h10*dt*(b[k][j]-prev[k][j])/(b[0]-prev[0])+h01*b[k][j]+h11*dt*(i===keys.length-2?0:(next[k][j]-a[k][j])/(next[0]-a[0])));
 const target=interp(2),raw=interp(1),widen=aspect<1?1.75:1;
 return {pos:raw.map((x,j)=>target[j]+(x-target[j])*widen),target,roll:Math.sin(t*.045)*.025};
}

// The displayed CRT example: pairwise coprime moduli, explicit idempotent basis.
export const crtExample={moduli:[3,5,7],residues:[2,3,2],basis:[70,21,15],modulus:105};
export function combineCRT(residues){return ((residues.reduce((a,x,i)=>a+x*crtExample.basis[i],0)%105)+105)%105;}
