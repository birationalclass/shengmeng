import {createFilteredCycles} from './filtered-cycles.js?v=95';
import {createFilteredDemo} from './filtered-demo.js?v=92';
import {replaceMathContent} from './math-transitions.js?v=40';
// Z_r and B_r live in the filtered total complex, not in a single K-term.
// Regions encode subspace relations only; their areas never encode dimensions.
export function createFilteredView({viewport,diagram,point,board,math,language}){
 const R=String.raw,t=(zh,en)=>language()==='en'?en:zh;
 const demo=createFilteredDemo({host:diagram,point}),cycles=createFilteredCycles({host:diagram,point,math});
 let state=null,active=false,key='',topic='Z';const steps={Z:0,B:0};let inclusionStep=0;
 const pageIndex=()=>Math.max(1,state.r);
 const names={Z:[['逆像条件','Preimage condition'],['逐列条件','Column conditions'],['第一步','First step'],['随 r 变化','As r varies'],['具体例子','Example'],['非正指标','Nonpositive indices']],B:[['像与交集','Image and intersection'],['代表元条件','Representative condition'],['一定是闭元','Always a cocycle'],['随 r 变化','As r varies'],['具体例子','Example'],['非正指标','Nonpositive indices']]};
 function inclusionExposition(){
  const entries=[
   {name:['边界项','Boundary term'],f:[R`n=p+q,\quad r,s\in\mathbb Z`,R`x\in B_s^{p,q}\Longrightarrow x=Db\in F^pC^n`,R`Dx=D^2b=0\in F^{p+r}C^{n+1}`,R`B_s^{p,q}\subseteq F^pC^n\cap\ker D\subseteq Z_r^{p,q}`],note:t('任何这里的边界都是总复形的闭元，所以满足每一个 Zᵣ 的像条件。图中沿用 1.12 的例子，蓝色像属于 B₂¹¹，因此也属于 Zᵣ¹¹。','Every such boundary is a total cocycle, so it satisfies the image condition for every Zᵣ. In the example from 1.12, the blue images lie in B₂¹¹ and hence in Zᵣ¹¹.')},
   {name:['高滤过项','Higher-filtration term'],f:[R`z\in Z_{r-1}^{p+1,q-1}\Longleftrightarrow\begin{cases}z\in F^{p+1}C^n,\\Dz\in F^{(p+1)+(r-1)}C^{n+1}=F^{p+r}C^{n+1},\end{cases}`,R`F^{p+1}C^n\subseteq F^pC^n`,R`Z_{r-1}^{p+1,q-1}=Z_r^{p,q}\cap F^{p+1}C^n\subseteq Z_r^{p,q}`],note:t('总次数仍为 (p+1)+(q−1)=p+q；两个子空间要求相同的像条件。','The total degree remains (p+1)+(q−1)=p+q; both subspaces impose the same condition on the image.')},
   {name:['用于定义各页','Use in defining the pages'],f:[R`Z_{r-1}^{p+1,q-1}\subseteq Z_r^{p,q},\qquad B_{r-1}^{p,q}\subseteq Z_r^{p,q}`,R`Z_{r-1}^{p+1,q-1}+B_{r-1}^{p,q}\subseteq Z_r^{p,q}`,R`E_r^{p,q}:=\frac{Z_r^{p,q}}{Z_{r-1}^{p+1,q-1}+B_{r-1}^{p,q}}\quad(r\ge0)`],note:t('分母是分子的子空间，因此 2.1 的商有定义。只证明 Bᵣ 包含于 Zᵣ 还没有检查完整的分母。','The denominator is a subspace of the numerator, so the quotient in 2.1 is defined. Bᵣ ⊆ Zᵣ alone does not check the entire denominator.')},
   {name:['图中的投影','Projection in the diagram'],f:[R`\pi_p:F^pC^{p+q}\longrightarrow K^{p,q},\qquad a\longmapsto a_p`,R`\ker(\pi_p|_{Z_r^{p,q}})=Z_{r-1}^{p+1,q-1}`,R`\varphi_r:\pi_p(Z_r^{p,q})\longrightarrow E_r^{p,q},\quad\pi_p(a)\longmapsto[a]_r`,R`\ker\varphi_r=\pi_p(B_{r-1}^{p,q})`,R`E_r^{p,q}\cong\frac{\pi_p(Z_r^{p,q})}{\pi_p(B_{r-1}^{p,q})}`],note:t('前两步保证这个映射不依赖提升 a；它满射，且核正是所示边界的投影。动画中从 K 小块分出的子空间是 πₚ(Zᵣ)，不是 Zᵣ 本身。','The preceding inclusions make the map independent of the lift a. It is surjective with the displayed kernel. The subspace split off from a K tile is πₚ(Zᵣ), not Zᵣ itself.')}
  ],entry=entries[inclusionStep];
  const note=entry.note.replace(/πₚ\(Zᵣ\)|B₂¹¹|Zᵣ¹¹|Bᵣ|Zᵣ/g,k=>math({'πₚ(Zᵣ)':R`\pi_p(Z_r^{p,q})`,'B₂¹¹':R`B_2^{1,1}`,'Zᵣ¹¹':R`Z_r^{1,1}`,'Bᵣ':'B_r','Zᵣ':'Z_r'}[k]));
  board.dataset.currentProofTopic='inclusions';board.dataset.currentProofStep=String(inclusionStep);
  replaceMathContent(board,`<nav class="proof-steps" aria-label="${t('证明关键步骤','Key proof steps')}">${entries.map((e,i)=>`<button data-inclusion-proof="${i}" aria-pressed="${i===inclusionStep}">${i+1}. ${t(...e.name)}</button>`).join('')}</nav><div class="operation-content">${entry.f.map(f=>`<div class="operation-equation">${math(f,true)}</div>`).join('')}</div><p class="operation-note">${note}</p><p class="operation-note proof-reference"><a href="https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/McCleary-UGSS.pdf#page=48" target="_blank" rel="noopener">McCleary, Theorem 2.6, pp. 34–35</a></p>`);
 }
 function exposition(){
  if(state.annotationStep===3){inclusionExposition();return;}
  const r=pageIndex(),n=state.n,p=state.p,q=n-p,i=steps[topic];
  const proof=topic==='Z'?[
   [R`r\in\mathbb Z,\quad n=p+q`,R`Z_r^{p,q}:=\{a\in F^pC^n:Da\in F^{p+r}C^{n+1}\}`,R`Z_r^{p,q}=\ker\big(F^pC^n\xrightarrow{D}C^{n+1}\xrightarrow{\pi}C^{n+1}/F^{p+r}C^{n+1}\big)`],
   [R`a=\sum_{i\ge p}a_i,\qquad a_i\in K^{i,n-i}`,R`(Da)_i=\delta_1a_{i-1}+\delta_2a_i`,R`a\in Z_r^{p,q}\iff\delta_1a_{i-1}+\delta_2a_i=0\quad(p\le i<p+r)`,R`a_i=0\quad(i<p)`],
   [R`Z_0^{p,q}=F^pC^n`,R`a\in Z_1^{p,q}\iff\delta_2a_p=0`,R`a\in Z_2^{p,q}\iff\begin{cases}\delta_2a_p=0,\\\delta_1a_p+\delta_2a_{p+1}=0.\end{cases}`],
   [R`F^{p+r+1}C^{n+1}\subseteq F^{p+r}C^{n+1}`,R`Z_{r+1}^{p,q}\subseteq Z_r^{p,q}`,R`p+r>n+1\ \Longrightarrow\ Z_r^{p,q}=F^pC^n\cap\ker D`]
  ]:[
   [R`r\in\mathbb Z,\quad n=p+q`,R`B_r^{p,q}:=F^pC^n\cap D(F^{p-r}C^{n-1})`,R`x\in B_r^{p,q}\iff\exists b\in F^{p-r}C^{n-1}:x=Db\in F^pC^n`],
   [R`b=\sum_{i\ge p-r}b_i,\qquad b_i\in K^{i,n-1-i}`,R`(Db)_i=\delta_1b_{i-1}+\delta_2b_i`,R`Db\in F^pC^n\iff\delta_1b_{i-1}+\delta_2b_i=0\quad(i<p)`],
   [R`B_0^{p,q}=D(F^pC^{n-1})`,R`x=Db\ \Longrightarrow\ Dx=D^2b=0`,R`B_r^{p,q}\subseteq F^pC^n\cap\ker D\subseteq Z_s^{p,q}\quad(s\ge0)`],
   [R`F^{p-r}C^{n-1}\subseteq F^{p-r-1}C^{n-1}`,R`B_r^{p,q}\subseteq B_{r+1}^{p,q}`,R`r\ge p\ \Longrightarrow\ B_r^{p,q}=F^pC^n\cap D(C^{n-1})`]
  ];
  const note=topic==='Z'?[
   t(`${math('D^{-1}')} 表示子空间的逆像，不要求 ${math('D')} 可逆。${math('Z_r^{p,q}')} 中的元素是总上链；通常不要求 ${math('Da=0')}，也不能把它当成 ${math('E_r')} 页上的核。`,`${math('D^{-1}')} denotes a preimage, not an inverse map. Elements of ${math('Z_r^{p,q}')} are total cochains; ${math('Da')} need not vanish. This is not a kernel on the ${math('E_r')} page.`),
   t('需要检查各列分量之和的抵消。Zᵣ 通常不能表示为若干 K 小块的直和。','The sums of components must cancel in the excluded columns. In general Zᵣ is not a direct sum of selected K-terms.'),
   t('r=1 只检查首列；r=2 还要检查下一列。总次数 n 之外的分量为零。','For r=1 only the first column is tested; r=2 also tests the next. Components outside total degree n are zero.'),
   t('r 增大时像的条件更强，Zᵣ 缩小；目标滤过为零时，就要求 Da=0。','As r grows, the image condition becomes stronger and Zᵣ decreases. When the target filtration is zero, Da must be zero.')
  ]:[
   r===0?t(`本图取 ${math('r=0')}。${math('D')} 保持滤过，所以 ${math('D(F^pC^{n-1})')} 已包含在 ${math('F^pC^n')} 中，恰好等于 ${math('B_0^{p,q}')}。一般 ${math('r')} 的定义仍需取交集。`,`Here ${math('r=0')}. Since ${math('D')} preserves the filtration, ${math('D(F^pC^{n-1})')} already lies in ${math('F^pC^n')} and equals ${math('B_0^{p,q}')}. For general ${math('r')} the intersection is still required.`):t('D 的像还需落入 FᵖCⁿ，交集才是 Bᵣ。整个 Fᵖ⁻ʳCⁿ⁻¹ 并不一定映入 Bᵣ。','Intersect the image of D with FᵖCⁿ to obtain Bᵣ. The whole source need not map into Bᵣ.'),
   t('b 可以从 p−r 列开始，但 Db 的所有 p 列之前的分量必须抵消。','The representative b may start in column p−r, but all components of Db before column p must cancel.'),
   t('这是总复形中的边界，因此由 D²=0 自动得到闭性。','These are boundaries in the total complex; D²=0 makes them cocycles.'),
   t('r 增大时允许更多来源，所以 Bᵣ 增大。注意 Eᵣ 的分母使用 Bᵣ₋₁。','As r grows, more source columns are allowed and Bᵣ increases. The denominator of Eᵣ uses Bᵣ₋₁.')
  ];
  proof.push(topic==='Z'?[
   R`u,s\in K^{1,1},\quad v\in K^{2,0}`,
   R`\delta_1u=t,\quad\delta_2s=w,\quad\delta_1v=z,\quad\delta_2v=-t`,
   R`t\in K^{2,1},\ w\in K^{1,2},\ z\in K^{3,0}`,
   R`a_1=u+v,\quad a_2=u,\quad a_3=s,\quad a_4=2(u+v)`,
   R`Da_1=z,\quad Da_2=t,\quad Da_3=w,\quad Da_4=2z`,
   R`a_1,a_4\in Z_2^{1,1},\qquad a_2,a_3\notin Z_2^{1,1}`
  ]:[
   R`\alpha\in K^{0,1},\quad\beta\in K^{1,0},\quad c\in K^{0,2},\quad b\in K^{1,1}`,
   R`\delta_2\alpha=c,\quad\delta_2\beta=b,\quad\delta_1\alpha=\delta_1\beta=0`,
   R`b_1=\beta,\quad b_2=\alpha,\quad b_3=\alpha+\beta,\quad b_4=2\beta`,
   R`Db_1=b,\quad Db_2=c,\quad Db_3=c+b,\quad Db_4=2b`,
   R`Db_1,Db_4\in B_2^{1,1},\qquad Db_2,Db_3\notin B_2^{1,1}`
  ]);
  note.push(t((topic==='Z'?'u,s,v,t,w,z':'α,β,c,b')+' 为基向量；未列出的微分均为零。圆点代表整条总上链，位置只示意归属，不是某个 K 分量。',(topic==='Z'?'u,s,v,t,w,z':'α,β,c,b')+' are basis vectors, with all unlisted differentials zero. Each dot represents an entire total cochain; its position indicates membership, not a K-component.'));
  proof.push(topic==='Z'?[
   R`r\le0,\qquad n=p+q`,
   R`D(F^pC^n)\subseteq F^pC^{n+1}\subseteq F^{p+r}C^{n+1}`,
   R`Z_r^{p,q}=F^pC^n\qquad(r\le0)`,
   R`Z_{-1}^{p+1,q-1}=F^{p+1}C^n`
  ]:[
   R`r\le0,\qquad n=p+q`,
   R`D(F^{p-r}C^{n-1})\subseteq F^{p-r}C^n\subseteq F^pC^n`,
   R`B_r^{p,q}=D(F^{p-r}C^{n-1})\qquad(r\le0)`,
   R`B_{-1}^{p,q}=D(F^{p+1}C^{n-1})\subseteq F^{p+1}C^n`
  ]);
  note.push(t('Z、B 的公式对每个整数 r 都有意义。r≤0 时像条件自动满足；上面说明了相应化简。负滤过层也不应误认为零：第一象限下，j≤0 时 FʲCⁿ=Cⁿ。','The formulas for Z and B make sense for every integer r. For r≤0 the relevant image containment is automatic, giving the displayed simplifications. A negative filtration level is not zero: in the first quadrant, FʲCⁿ=Cⁿ for j≤0.'));
  board.dataset.currentProofTopic=topic;board.dataset.currentProofStep=String(i);
  replaceMathContent(board,`<nav class="proof-steps" aria-label="${t('证明关键步骤','Key proof steps')}">${names[topic].map((name,j)=>`<button data-filter-step="${j}" aria-pressed="${i===j}">${j+1}. ${t(...name)}</button>`).join('')}</nav><div class="operation-content">${proof[i].map(f=>`<div class="operation-equation">${math(f,true)}</div>`).join('')}</div><p class="operation-note">${note[i]}</p><p class="filtered-example">${math(R`n=${n},\quad p=${p},\quad q=${q},\quad r=${r}`)}</p><p class="operation-note">${topic==='Z'?t(`虚框内蓝点是 ${math('Z_2^{1,1}')} 中的示例。它们的像落入 ${math('F^3C^3')}；黄点的像在 ${math('C^3')} 中但不在 ${math('F^3C^3')} 中。`,`The outlined blue dots are samples in ${math('Z_2^{1,1}')}. Their images lie in ${math('F^3C^3')}; gold images lie in ${math('C^3')} outside ${math('F^3C^3')}.`):t('圆点代表总上链；蓝色像满足滤过条件，黄色像不满足。轨迹表示总微分 D。','Dots represent total cochains: blue images meet the filtration condition; gold images do not. Tracks represent the total differential D.')}</p><p class="operation-note proof-reference"><a href="https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/McCleary-UGSS.pdf#page=48" target="_blank" rel="noopener">McCleary, Theorem 2.6, p. 34</a></p>`);
 }
 board.addEventListener('click',e=>{const proof=e.target.closest('[data-inclusion-proof]');if(proof&&active&&state.annotationStep===3){e.stopPropagation();inclusionStep=Number(proof.dataset.inclusionProof);inclusionExposition();return;}const button=e.target.closest('[data-filter-step]');if(!active||!button)return;e.stopPropagation();steps[topic]=Number(button.dataset.filterStep);exposition();});
 return {enter:()=>{if(topic==='Z')cycles.enter();},play:()=>topic==='Z'?cycles.play():demo.play(topic,true),stop:()=>{demo.clear();cycles.stop();},clear:()=>{demo.clear();cycles.clear();},isPlaying:()=>demo.isPlaying()||cycles.isPlaying(),sync(s){
  state=s;active=!s.cover&&s.module==='learn'&&s.step===6&&s.annotationStep>=1&&s.annotationStep<=3;
  viewport.classList.toggle('has-filtered-grid',active);
  if(!active){key='';demo.clear();cycles.clear();return;}
  topic=s.annotationStep===1?'Z':'B';const next=[s.step,topic,s.n,s.p,pageIndex(),language()].join(':');
  if(next!==key){const changed=key.split(':').slice(0,5).join(':')!==next.split(':').slice(0,5).join(':');key=next;if(changed){demo.clear();cycles.clear();}}exposition();
 }};
}
