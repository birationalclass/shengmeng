import {replaceMathContent} from './math-transitions.js?v=40';
import {cohomologyExposition} from './cohomology-view.js?v=38';
// This panel owns its proof steps. Navigating a proof never advances a notebook
// statement, changes a page, or cancels a diagram animation.
export function createDifferentialProof({board,math,language}){
 const R=String.raw,t=(zh,en)=>language()==='en'?en:zh;
 let context=null,key='',topic='d0',steps={d0:0,d1:0,dr:0},phase=3;
 const explanations={
  d0:[
   {name:['诱导到商','Descend to the quotient'],f:[R`D(F^pC^n)\subseteq F^pC^{n+1}`,R`a'-a\in F^{p+1}C^n\ \Longrightarrow\ Da'-Da\in F^{p+1}C^{n+1}`,R`d_0^{p,q}[a]_0:=[Da]_0,\qquad n=p+q`],note:['代表元改变一个下一层滤过中的元素，其像也只改变一个下一层元素，所以 d₀ 良定义。','Changing a representative by the next filtration changes its image by the next filtration. Thus d₀ is well-defined.']},
   {name:['自然同构','Natural identification'],f:[R`a=\sum_{i\ge p}a_i,\qquad a_i\in K^{i,n-i}`,R`\Phi_0^{p,q}:E_0^{p,q}\xrightarrow{\sim}K^{p,q},\qquad\Phi_0^{p,q}([a]_0):=a_p`,R`\ker(F^pC^n\longrightarrow K^{p,q})=F^{p+1}C^n`],note:['取第 p 列分量给出满射；其核恰是分母。这是给定双分次产生的自然同构。','Projection to column p is surjective, with kernel equal to the denominator. The bigrading gives this natural isomorphism.']},
   {name:['计算第 p 列','Compute column p'],f:[R`D:=\delta_1+\delta_2`,R`\delta_1a_i\in K^{i+1,n-i},\qquad\delta_2a_i\in K^{i,n-i+1}`,R`(Da)_p=\delta_2a_p\qquad(a_i=0\text{ for }i<p)`,R`\delta_1(F^pC^n)\subseteq F^{p+1}C^{n+1}`],note:['横向微分的像在下一列；取关联分次时消失。保持第 p 列的分量是 δ₂aₚ。','The horizontal image lies in the next column and vanishes in the associated graded. The column-p component is δ₂aₚ.']},
   {name:['交换恒等式','Commuting identity'],f:[R`\Phi_0^{p,q+1}\circ d_0^{p,q}=\delta_2^{p,q}\circ\Phi_0^{p,q}`,R`d_0^{p,q}=(\Phi_0^{p,q+1})^{-1}\delta_2^{p,q}\Phi_0^{p,q}`],note:['d₀ 与 δ₂ 经 Φ₀ 对应。D 作用于总复形，仍为 δ₁+δ₂；这里并没有将 D 改成 δ₂。','Φ₀ identifies d₀ with δ₂. On the total complex D remains δ₁+δ₂; the quotient does not replace D by δ₂.']}
  ],
  d1:[
   {name:['闭代表元','Closed representatives'],f:[R`a\in K^{p,q},\quad\delta_2a=0`,R`\delta_2\delta_1a=-\delta_1\delta_2a=0`],note:['反交换关系保证 δ₁a 仍为纵向闭元，因此它确定 E₁ 中的类。','Anticommutation makes δ₁a a vertical cocycle, so it determines a class in E₁.']},
   {name:['代表元无关','Independence of representative'],f:[R`a'=a+\delta_2b,\qquad b\in K^{p,q-1}`,R`\delta_1a'-\delta_1a=-\delta_2\delta_1b`,R`[\delta_1a']_1=[\delta_1a]_1`],note:['差值是一个纵向边界，所以 d₁ 不依赖闭代表元的选择。','The difference is a vertical boundary, so d₁ is independent of the closed representative.']},
   {name:['由 D 给出','Induced by D'],f:[R`Da=\delta_1a\in F^{p+1}C^{p+q+1}`,R`d_1^{p,q}[a]_1=[Da]_1=[\delta_1a]_1`,R`d_1^{p+1,q}d_1^{p,q}[a]_1=[\delta_1^2a]_1=0`],note:['这与滤过总复形中由 D 诱导的定义一致。d₁ 作用在 E₁ 上。','This agrees with the definition induced by D on the filtered total complex. The domain of d₁ is E₁.']}
  ],
  dr:[
   {name:['分子映到分子','Map the numerator'],f:[R`n=p+q,\quad r\ge1,\quad a\in Z_r^{p,q}`,R`Da\in F^{p+r}C^{n+1},\qquad D(Da)=0`,R`Da\in Z_r^{p+r,q-r+1}`],note:['总次数提高一，滤过至少提高 r；由 D²=0 可知像满足目标分子的条件。','The total degree rises by one and the filtration rises by at least r. D²=0 gives the target numerator condition.']},
   {name:['分母映到分母','Map the denominator'],f:[R`z\in Z_{r-1}^{p+1,q-1}\ \Longrightarrow\ z\in F^{p+1}C^n,\ Dz\in F^{p+r}C^{n+1}`,R`Dz\in F^{p+r}C^{n+1}\cap D(F^{p+1}C^n)=B_{r-1}^{p+r,q-r+1}`,R`b\in B_{r-1}^{p,q}\ \Longrightarrow\ Db=0`],note:['源分母的第一部分映入目标边界项，第二部分映为零。因此 D 诱导商上的映射。','The first part of the source denominator maps into the target boundary term; the second maps to zero. D therefore induces a quotient map.']},
   {name:['良定义与次数','Well-definedness and degree'],f:[R`a'=a+z+b\ \Longrightarrow\ [Da']_r=[Da]_r`,R`d_r^{p,q}:E_r^{p,q}\longrightarrow E_r^{p+r,q-r+1}`,R`d_r^{p,q}[a]_r:=[Da]_r`,R`(p+r)+(q-r+1)=p+q+1`],note:['此处 z、b 分别属于上一步列出的两个源分母子空间。页号 r 没有改变。','Here z and b belong to the two source-denominator subspaces in the preceding step. The page index r is unchanged.']},
   {name:['平方为零','Square zero'],f:[R`d_r^{p+r,q-r+1}d_r^{p,q}[a]_r=[D^2a]_r=0`,R`E_{r+1}^{p,q}\cong\frac{\ker(d_r^{p,q})}{\operatorname{im}(d_r^{p-r,q+r-1})}`],note:['平方为零来自同一个 D²=0。下一页是这个微分的上同调；该同构由滤过商空间的构造得到。','Square zero follows from the same identity D²=0. The filtered-quotient construction identifies the next page with this cohomology.']}
  ]
 };
 function properties(){
  const section=context.state.step,zero=context.state.module==='learn'&&section===3;
  const formulas=zero?[
   R`\Phi_0^{p,q}:E_0^{p,q}\xrightarrow{\sim}K^{p,q},\qquad\Phi_0^{p,q}([a]_0):=a_p`,
   R`\Phi_0^{p,q+1}d_0^{p,q}=\delta_2^{p,q}\Phi_0^{p,q},\qquad d_0^2=0`
  ]:section===4?[
   R`E_1^{p,q}\cong H^q(K^{p,\bullet},\delta_2),\qquad d_1^2=0`,
   R`E_2^{p,q}\cong H^p(E_1^{\bullet,q},d_1)`
  ]:[
   R`d_r^{p+r,q-r+1}d_r^{p,q}=0`,
   R`E_{r+1}^{p,q}\cong\frac{\ker d_r^{p,q}}{\operatorname{im}d_r^{p-r,q+r-1}}`
  ];
  return `<section class="key-properties"><h4>${t('关键性质','Key properties')}</h4>${formulas.map(f=>`<div class="operation-equation">${math(f,true)}</div>`).join('')}</section>`;
 }
 function paint(){
  const allTopics=[['d0',t('d₀ 的来源','Origin of d₀')],['d1',t('d₁ 的良定义','Well-defined d₁')],['dr',t('dᵣ 的良定义','Well-defined dᵣ')],['cohom',t('取上同调','Cohomology')]];
  const zero=context?.state.module==='learn'&&context.state.step===3;
  const topics=zero?allTopics.filter(([id])=>id==='d0'):allTopics;
  if(zero)topic='d0';
  let html=properties()+`<nav class="proof-topics" aria-label="${t('数学阐述主题','Mathematical exposition topics')}">${topics.map(([id,name])=>`<button data-proof-topic="${id}" aria-pressed="${topic===id}">${name.replace(/d([₀₁ᵣ])/g,(_,r)=>math('d_{'+({'₀':0,'₁':1,'ᵣ':'r'}[r])+'}'))}</button>`).join('')}</nav>`;
  if(topic==='cohom')html+=cohomologyExposition({r:context.construction?.r??Math.max(0,context.current-1),phase,point:context.point,math,t});
  else{
   const entries=explanations[topic],entry=entries[steps[topic]];
   html+=`<nav class="proof-steps" aria-label="${t('证明关键步骤','Key proof steps')}">${entries.map((e,i)=>`<button data-proof-step="${i}" aria-pressed="${steps[topic]===i}">${i+1}. ${t(...e.name)}</button>`).join('')}</nav><div class="proof-body"><div class="operation-content evolution-exposition">${entry.f.map(f=>`<div class="operation-equation">${math(f,true)}</div>`).join('')}</div><p class="operation-note">${t(...entry.note)}</p></div>`;
  }
  replaceMathContent(board,html);board.dataset.currentProofTopic=topic;board.dataset.currentProofStep=topic==='cohom'?phase:steps[topic];
 }
 board.addEventListener('click',e=>{
  const button=e.target.closest('[data-proof-topic],[data-proof-step],[data-co-phase]');if(!button||!context)return;
  e.stopPropagation();if(button.dataset.proofTopic){topic=button.dataset.proofTopic;}else if(button.dataset.proofStep!==undefined)steps[topic]=Number(button.dataset.proofStep);else phase=Number(button.dataset.coPhase);paint();
 });
 return {render(c){context=c;const nextKey=`${c.state.module}:${c.state.step}`;if(nextKey!==key){key=nextKey;topic=c.state.module==='learn'&&c.state.step===5?'dr':c.construction?'cohom':c.state.module==='learn'&&c.state.step===4?'d1':'d0';}paint();},reset(){key='';context=null;steps={d0:0,d1:0,dr:0};phase=3;}};
}
