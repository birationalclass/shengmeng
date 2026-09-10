import {replaceMathContent} from './math-transitions.js?v=64';
import {cohomologyExposition} from './cohomology-view.js?v=38';
// This panel owns its proof steps. Navigating a proof never advances a notebook
// statement, changes a page, or cancels a diagram animation.
export function createDifferentialProof({board,math,language}){
 const R=String.raw,t=(zh,en)=>language()==='en'?en:zh;
 let context=null,key='',topic='d0',steps={e0:0,e1:0,d0:0,d1:0,dr:0},phase=3;
 const explanations={
  e0:[
   {name:['元素与记号','Elements and notation'],f:[R`[a]_0:=a+F^{p+1}C^{p+q}\in E_0^{p,q},\quad a\in F^pC^{p+q}`,R`\begin{array}{rcl}\Phi_0^{p,q}:K^{p,q}&\xrightarrow{\sim}&E_0^{p,q}\\a&\longmapsto&[a]_0\end{array}`],note:['当 a∈K^{p,q} 时，先通过直和因子的自然嵌入将 a 视为 F^pC^{p+q} 中的元素，再取陪集。此处 [a]₀ 是滤过商中的类，无须 a 满足闭性条件。','For a∈K^{p,q}, first regard a as an element of F^pC^{p+q} via the natural inclusion of the direct summand, then take its coset. Here [a]₀ is a class in a filtration quotient; no cocycle condition on a is required.']},
   {name:['同构与逆映射','The isomorphism and its inverse'],f:[R`n=p+q,\qquad F^pC^n=K^{p,q}\oplus F^{p+1}C^n`,R`a=\sum_{i\ge p}a_i,\qquad a_i\in K^{i,n-i}`,R`(\Phi_0^{p,q})^{-1}([a]_0):=a_p`],note:['每个陪集都有唯一一个属于 K^{p,q} 的代表元，因此该映射是典范同构。E₀ 的定义仍然是商空间；动画采用此同构在同一位置标示两者。','Every coset has exactly one representative in K^{p,q}, so the map is a canonical isomorphism. E₀ remains defined as a quotient; the animation uses this identification to label both at the same position.']},
   {name:['代表元无关','Independence of representative'],f:[R`a,a'\in F^pC^{p+q}`,R`[a']_0=[a]_0\iff a'-a\in F^{p+1}C^{p+q}`,R`a'-a\in F^{p+1}C^{p+q}\iff a'_p=a_p`],note:['更高列的分量不会改变第 p 列分量，故逆映射不依赖代表元。','Higher-column components do not change the column-p component, so the inverse is independent of the representative.']}
  ],
  d0:[
   {name:['诱导到商','Descend to the quotient'],f:[R`d_0:=\operatorname{Gr}_F D,\qquad a,a'\in F^pC^n`,R`D(F^{p+1}C^n)\subseteq F^{p+1}C^{n+1}`,R`a'-a\in F^{p+1}C^n\ \Longrightarrow\ Da'-Da\in F^{p+1}C^{n+1}`,R`d_0^{p,q}[a]_0:=[Da]_0,\qquad n=p+q`],note:['D 保持下一层滤过，故 d₀ 不依赖代表元。','D preserves the next filtration layer, so d₀ is independent of the representative.']},
   {name:['只保留纵向分量','The vertical component survives'],f:[R`a\in K^{p,q},\qquad Da=\delta_1^{p,q}a+\delta_2^{p,q}a`,R`\delta_1^{p,q}a\in K^{p+1,q}\subseteq F^{p+1}C^{p+q+1}`,R`[Da]_0=[\delta_2^{p,q}a]_0`],note:['横向分量在商中为零；这并不是总复形上 D=δ₂。','The horizontal component vanishes in the quotient; this does not mean D=δ₂ on the total complex.']},
   {name:['与同构相容','Compatibility with the isomorphism'],f:[R`d_0^{p,q}\circ\Phi_0^{p,q}=\Phi_0^{p,q+1}\circ\delta_2^{p,q}`,R`d_0^{p,q}=\Phi_0^{p,q+1}\circ\delta_2^{p,q}\circ(\Phi_0^{p,q})^{-1}`,R`(K^{\bullet,\bullet},\delta_2)\cong(E_0^{\bullet,\bullet},d_0)`],note:['d₀ 对应 δ₂，而非总微分 D。一般只需滤过复形 (C,F,D) 即可构造 (E₀,d₀)，无须预先将 D 分解。','d₀ corresponds to δ₂, not the total differential D. In general the filtered complex (C,F,D) defines (E₀,d₀) without a prior decomposition of D.']},
   {name:['平方为零','Square zero'],f:[R`d_0^{p,q+1}d_0^{p,q}[a]_0=[D^2a]_0=0`],note:['D²=0 下降为商上的 d₀²=0。','D²=0 descends to d₀²=0 on the quotient.']}
  ],
  e1:[
   {name:['上同调：核模像','Cohomology: kernel modulo image'],f:[R`E_1^{p,q}:=H^q(E_0^{p,\bullet},d_0)=\frac{\ker(d_0^{p,q})}{\operatorname{im}(d_0^{p,q-1})}`,R`E_1^{p,q}\cong H^q(K^{p,\bullet},\delta_2)=\frac{\ker(\delta_2^{p,q})}{\operatorname{im}(\delta_2^{p,q-1})}`,R`[a]_1:=[a]_0+\operatorname{im}(d_0^{p,q-1}),\quad a\in\ker(\delta_2^{p,q})`],note:['第一行定义 E₁；第二行通过 Φ₀ 诱导的自然同构计算。分子与分母分别是纵向出射映射的核、纵向入射映射的像。','The first line defines E₁; the second computes it via the natural isomorphism induced by Φ₀. The numerator is the kernel of the outgoing vertical map; the denominator is the image of the incoming vertical map.']},
   {name:['元素与代表元','Elements and representatives'],f:[R`a,a'\in K^{p,q},\quad\delta_2^{p,q}a=\delta_2^{p,q}a'=0`,R`[a]_1:=[a]_0+\operatorname{im}(d_0^{p,q-1})\in E_1^{p,q}`,R`[a]_1\ \longleftrightarrow\ a+\operatorname{im}(\delta_2^{p,q-1})`,R`[a]_1=[a']_1\iff a'-a\in\operatorname{im}(\delta_2^{p,q-1})`],note:['这里通过自然同构采用 K 中的纵向闭元作代表；相差一个纵向边界表示同一个 E₁ 类。','Using the natural isomorphism, we represent E₁ classes by vertical cocycles in K; two such cocycles give the same class exactly when their difference is a vertical boundary.']}
  ],
  d1:[
   {name:['闭代表元','Closed representatives'],f:[R`a\in K^{p,q},\quad\delta_2a=0`,R`\delta_2\delta_1a=-\delta_1\delta_2a=0`],note:['反交换关系保证 δ₁a 仍为纵向闭元。','Anticommutation makes δ₁a a vertical cocycle.']},
   {name:['代表元无关','Independence of representative'],f:[R`a'=a+\delta_2b,\qquad b\in K^{p,q-1}`,R`\delta_1a'-\delta_1a=-\delta_2\delta_1b`,R`[\delta_1a']_1=[\delta_1a]_1`],note:['差值是一个纵向边界，所以 d₁ 不依赖闭代表元的选择。','The difference is a vertical boundary, so d₁ is independent of the closed representative.']},
   {name:['由 D 给出','Induced by D'],f:[R`Da=\delta_1a\in F^{p+1}C^{p+q+1}`,R`d_1^{p,q}[a]_1=[Da]_1=[\delta_1a]_1`,R`d_1^{p+1,q}d_1^{p,q}[a]_1=[\delta_1^2a]_1=0`],note:['这与 D 诱导的定义一致。','This agrees with the definition induced by D.']}
  ],
  dr:[
   {name:['分子映到分子','Map the numerator'],f:[R`n=p+q,\quad r\ge1,\quad a\in Z_r^{p,q}`,R`Da\in F^{p+r}C^{n+1},\qquad D(Da)=0`,R`Da\in Z_r^{p+r,q-r+1}`],note:['D²=0 保证像满足目标分子的条件。','D²=0 gives the target numerator condition.']},
   {name:['分母映到分母','Map the denominator'],f:[R`z\in Z_{r-1}^{p+1,q-1}\ \Longrightarrow\ z\in F^{p+1}C^n,\ Dz\in F^{p+r}C^{n+1}`,R`Dz\in F^{p+r}C^{n+1}\cap D(F^{p+1}C^n)=B_{r-1}^{p+r,q-r+1}`,R`b\in B_{r-1}^{p,q}\ \Longrightarrow\ Db=0`],note:['源分母的第一部分映入目标边界项，第二部分映为零。因此 D 诱导商上的映射。','The first part of the source denominator maps into the target boundary term; the second maps to zero. D therefore induces a quotient map.']},
   {name:['良定义与次数','Well-definedness and degree'],f:[R`a'=a+z+b\ \Longrightarrow\ [Da']_r=[Da]_r`,R`d_r^{p,q}:E_r^{p,q}\longrightarrow E_r^{p+r,q-r+1}`,R`d_r^{p,q}[a]_r:=[Da]_r`,R`(p+r)+(q-r+1)=p+q+1`],note:['z、b 属于上一步的两个源分母子空间。','Here z and b belong to the two source-denominator subspaces above.']},
   {name:['平方为零','Square zero'],f:[R`d_r^{p+r,q-r+1}d_r^{p,q}[a]_r=[D^2a]_r=0`,R`E_{r+1}^{p,q}\cong\frac{\ker(d_r^{p,q})}{\operatorname{im}(d_r^{p-r,q+r-1})}`],note:['平方为零来自同一个 D²=0。下一页是这个微分的上同调；该同构由滤过商空间的构造得到。','Square zero follows from the same identity D²=0. The filtered-quotient construction identifies the next page with this cohomology.']}
  ]
 };
 function noteMath(text){return text.replace(/K\^\{p,q\}|F\^pC\^\{p\+q\}|a∈K\^\{p,q\}|\[a\]₀/g,token=>math({'a∈K^{p,q}':R`a\in K^{p,q}`,'[a]₀':R`[a]_0`}[token]||token));}
 function properties(){
  const section=context.state.step,zero=context.state.module==='learn'&&section===3;
  if(zero||context.state.module==='learn'&&section===4&&context.state.notePage===0)return '';
  const formulas=section===4?[
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
  const zeroTerm=zero&&context.state.notePage===0,firstTerm=context?.state.module==='learn'&&context.state.step===4&&context.state.notePage===0;
  const topics=zero?[[zeroTerm?'e0':'d0',zeroTerm?t('元素与典范同构','Elements and canonical identification'):t('d₀ 的来源','Origin of d₀')]]:allTopics;
  if(zero)topic=zeroTerm?'e0':'d0';else if(firstTerm)topic='e1';
  let html=properties()+`<nav class="proof-topics" aria-label="${t('数学阐述主题','Mathematical exposition topics')}">${topics.map(([id,name])=>`<button data-proof-topic="${id}" aria-pressed="${topic===id}">${name.replace(/d([₀₁ᵣ])/g,(_,r)=>math('d_{'+({'₀':0,'₁':1,'ᵣ':'r'}[r])+'}'))}</button>`).join('')}</nav>`;
  if(zero||firstTerm)html='';
  if(topic==='cohom')html+=cohomologyExposition({r:context.construction?.r??Math.max(0,context.current-1),phase,point:context.point,math,t});
  else{
   const entries=explanations[topic],entry=entries[steps[topic]];
   html+=`<nav class="proof-steps" aria-label="${t('证明关键步骤','Key proof steps')}">${entries.map((e,i)=>`<button data-proof-step="${i}" aria-pressed="${steps[topic]===i}">${i+1}. ${t(...e.name)}</button>`).join('')}</nav><div class="proof-body"><div class="operation-content evolution-exposition">${entry.f.map(f=>`<div class="operation-equation">${math(f,true)}</div>`).join('')}</div><p class="operation-note">${noteMath(t(...entry.note))}</p></div>`;
  }
  if(zero||firstTerm)html+=`<p class="operation-note proof-reference"><a href="https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/McCleary-UGSS.pdf#page=62" target="_blank" rel="noopener">McCleary, Theorem 2.15, pp. 48–49</a></p>`;
  replaceMathContent(board,html);board.dataset.currentProofTopic=topic;board.dataset.currentProofStep=topic==='cohom'?phase:steps[topic];
 }
 board.addEventListener('click',e=>{
  const button=e.target.closest('[data-proof-topic],[data-proof-step],[data-co-phase]');if(!button||!context)return;
  e.stopPropagation();if(button.dataset.proofTopic){topic=button.dataset.proofTopic;}else if(button.dataset.proofStep!==undefined)steps[topic]=Number(button.dataset.proofStep);else phase=Number(button.dataset.coPhase);paint();
 });
 return {render(c){context=c;const nextKey=`${c.state.module}:${c.state.step}:${c.state.notePage}`;if(nextKey!==key){key=nextKey;topic=c.state.module==='learn'&&c.state.step===5?'dr':c.state.module==='learn'&&c.state.step===4?(c.state.notePage===0?'e1':'d1'):c.construction?'cohom':'d0';}paint();},reset(){key='';context=null;steps={e0:0,e1:0,d0:0,d1:0,dr:0};phase=3;}};
}
