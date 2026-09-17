import {splittingTitles,splittingFormulas,splittingExpositions} from './hodge-splitting.js?v=157';
import {proofPanel} from './proof-panel.js?v=157';
const R=String.raw;
export const hodgeTitles=[['复微分形式','Complex differential forms'],['Dolbeault 双复形','Dolbeault double complex'],['Hodge–de Rham 谱序列','Hodge–de Rham spectral sequence'],['Hodge 滤过','Hodge filtration'],...splittingTitles];
export const hodgeContent={title:'Hodge decomposition',f:[
 R`\begin{gathered}\dim_{\mathbb C}X=m,\\\mathcal A^{p,q}(X),\quad 0\le p,q\le m,\\\mathcal A^n(X;\mathbb C)=\bigoplus_{p+q=n}\mathcal A^{p,q}(X)\end{gathered}`,
 R`\begin{gathered}K^{p,q}:=\mathcal A^{p,q}(X)\\\delta_1=\partial,\quad\delta_2=\bar\partial\\(C^\bullet,D)=(\mathcal A^\bullet(X;\mathbb C),d)\end{gathered}`,
 R`\begin{gathered}H_{\mathrm{dR}}^n(X;\mathbb C):=H^n(\mathcal A^\bullet(X;\mathbb C),d)\\=H^n(C^\bullet,D)\\[.5em]E_1^{p,q}\cong H^q(X,\Omega_X^p)\\E_1^{p,q}\Longrightarrow H_{\mathrm{dR}}^{p+q}(X;\mathbb C)\end{gathered}`,
 R`\begin{gathered}F^pC^n=\bigoplus_{a\ge p}\mathcal A^{a,n-a}(X)\\F^pH^n=\operatorname{im}\big(H^n(F^pC^\bullet)\to H^n\big)\\E_\infty^{p,q}\cong\operatorname{Gr}_F^pH^{p+q}\end{gathered}`,
 ...splittingFormulas
],text:'Hodge 分解与谱序列的关联分次。',note:'',proof:''};
export function hodgeSetup({page,math,t}){
 const text=page===0?t('设 X 是紧复流形。下列空间由光滑复值微分形式组成。','Let X be a compact complex manifold. The following spaces consist of smooth complex-valued differential forms.'):page===5?t('本条为一般双复形的代数命题。','This is an algebraic proposition for a general double complex.'):page>=4?t('进一步假设 X 为 Kähler 流形。','Assume in addition that X is Kähler.'):'';
 return text?`<div class="leray-setup"><p>${text}</p></div>`:'';
}
export function hodgeExposition({page,math,language}){
 const t=(z,e)=>language()==='en'?e:z,M=x=>math(x),eq=x=>`<div class="operation-equation">${math(x,true)}</div>`,p=x=>`<p>${x}</p>`;
 const ref='<a href="https://virtualmath1.stanford.edu/~conrad/shimsem/2013Notes/Littvhs.pdf#page=11" target="_blank" rel="noopener">Daniel Litt, Variations of Hodge Structure, Theorem 20 and Remark 21</a>';
 const base=t(`设 ${M('X')} 是复维数为 ${M('m')} 的紧复流形。`,`Let ${M('X')} be a compact complex manifold of complex dimension ${M('m')}.`);
 const kahler=t(`设 ${M('X')} 是紧 Kähler 流形，并记 ${M(R`H^n=H_{\mathrm{dR}}^n(X;\mathbb C)`)}；${M('F')} 为 3.4 的诱导滤过。`,`Let ${M('X')} be a compact Kähler manifold, write ${M(R`H^n=H_{\mathrm{dR}}^n(X;\mathbb C)`)}, and let ${M('F')} be the induced filtration of 3.4.`);

 const data=[
 {f:[R`\alpha=\sum_{|I|=p,\,|J|=q}\alpha_{I,J}\,dz_I\wedge d\bar z_J`],note:t(`${M(R`\mathcal A^{p,q}(X)`)} 是全局光滑 ${M('(p,q)')}-形式的向量空间；系数光滑，不要求全纯。${M(R`\Omega_X^p`)} 则表示全纯 p-形式层。`,`${M(R`\mathcal A^{p,q}(X)`)} is the vector space of global smooth ${M('(p,q)')}-forms; its coefficients need not be holomorphic. ${M(R`\Omega_X^p`)} denotes the sheaf of holomorphic p-forms.`),details:p('<strong>'+t('定义。','Definition.')+'</strong> '+base)+p(t('在局部全纯坐标中，按 dz 与其共轭微分的个数定义 (p,q)-型。全纯坐标变换保持型，因此这些局部定义相容。超出 0≤p,q≤m 的空间为零。','In local holomorphic coordinates, count dz and conjugate differentials to define type (p,q). Holomorphic coordinate changes preserve type, so the local definitions agree. Terms outside 0≤p,q≤m vanish.'))},
 {f:[R`\partial:K^{p,q}\to K^{p+1,q},\qquad\bar\partial:K^{p,q}\to K^{p,q+1}`,R`\partial^2=\bar\partial^2=0,\qquad\partial\bar\partial+\bar\partial\partial=0`],note:t('这正是第 1 节的第一象限双复形，且总复形是复值 de Rham 复形。','This is a first-quadrant double complex as in Section 1; its total complex is the complex-valued de Rham complex.'),details:p('<strong>'+t('命题。','Proposition.')+'</strong> '+base+t('则取上述 K、δ₁、δ₂ 得到双复形，其总微分为 d。','Then the displayed K, δ₁ and δ₂ form a double complex with total differential d.'))+p('<strong>'+t('证明。','Proof.')+'</strong> '+t('按型分解 d=∂+∂̄。将 d²=0 分别投影到双次数增加 (2,0)、(1,1)、(0,2) 的分量，得到三个双复形关系。','Decompose d=∂+∂̄ by type. Project d²=0 to its components of bidegrees (2,0), (1,1) and (0,2) to obtain the three double-complex identities.'))},
 {f:[R`H_{\mathrm{dR}}^n(X;\mathbb C)=\frac{\ker(d:\mathcal A^n\to\mathcal A^{n+1})}{\operatorname{im}(d:\mathcal A^{n-1}\to\mathcal A^n)}`],note:t(`de Rham 上同调是闭形式模去恰当形式；这里 ${M(R`\mathcal A^k=\mathcal A^k(X;\mathbb C)`)}。由 3.2 的 ${M(R`D=\partial+\bar\partial=d`)}，它就是双复形的总上同调。收敛只识别诱导 Hodge 滤过的关联分次；紧 Kähler 情形再由 3.5 的退化与 3.6 的典范分裂得到 3.7 的 Hodge 分解。`,`de Rham cohomology is closed forms modulo exact forms; here ${M(R`\mathcal A^k=\mathcal A^k(X;\mathbb C)`)}. Since ${M(R`D=\partial+\bar\partial=d`)} in 3.2, it is precisely the total cohomology of the double complex. Convergence identifies the graded pieces of the induced Hodge filtration; in the compact Kähler case, degeneration in 3.5 and the canonical splitting in 3.6 yield Hodge decomposition in 3.7.`),details:p('<strong>'+t('命题。','Proposition.')+'</strong> '+base+t('取 3.2 的 Dolbeault 双复形及列滤过，则其总上同调为 de Rham 上同调，并有下述收敛谱序列。','Take the Dolbeault double complex of 3.2 with its column filtration. Then its total cohomology is de Rham cohomology, and the following spectral sequence converges.'))+eq(hodgeContent.f[2])+p('<strong>'+t('证明。','Proof.')+'</strong> '+t('按型分解给出复形的自然识别','Decomposition by type gives the natural identification of complexes'))+eq(R`(\operatorname{Tot}K,D)=\left(\bigoplus_{p+q=\bullet}\mathcal A^{p,q}(X),\partial+\bar\partial\right)\cong(\mathcal A^\bullet(X;\mathbb C),d)`)+p(t(`该映射将各分量送到其和，因此在上同调上将 ${M(R`[(\alpha^{p,q})_{p+q=n}]_D`)} 送到 ${M(R`[\sum_{p+q=n}\alpha^{p,q}]_{\mathrm{dR}}`)}。de Rham 上同调按定义就是这个光滑形式复形的上同调。de Rham 定理还给出 ${M(R`H_{\mathrm{dR}}^n(X;\mathbb C)\cong H^n(X;\mathbb C)`)}，右端是奇异上同调。`,`The map sums the components, so on cohomology it sends ${M(R`[(\alpha^{p,q})_{p+q=n}]_D`)} to ${M(R`[\sum_{p+q=n}\alpha^{p,q}]_{\mathrm{dR}}`)}. By definition, de Rham cohomology is the cohomology of this smooth-form complex. The de Rham theorem further gives ${M(R`H_{\mathrm{dR}}^n(X;\mathbb C)\cong H^n(X;\mathbb C)`)}, with singular cohomology on the right.`))+p(t('先沿纵向取上同调。Dolbeault 引理给出下面的细层分解，所以全局截面计算层上同调：','First take vertical cohomology. The Dolbeault lemma gives the following fine resolution, whose global sections compute sheaf cohomology:'))+eq(R`0\to\Omega_X^p\to\mathcal A_X^{p,0}\xrightarrow{\bar\partial}\mathcal A_X^{p,1}\to\cdots`)+eq(R`E_1^{p,q}=H^q(\mathcal A^{p,\bullet}(X),\bar\partial)\cong H^q(X,\Omega_X^p)`)+p(t('第一象限收敛定理 2.9 给出以下同构，其中 F 是列滤过诱导的上同调滤过，下一小节将明确写出。这里尚不需要 Kähler 条件。','The first-quadrant convergence theorem 2.9 gives the following isomorphism. Here F is the cohomology filtration induced by the column filtration, written explicitly in the next subsection. No Kähler hypothesis is needed.'))+eq(R`E_\infty^{p,q}\cong\operatorname{Gr}_F^pH_{\mathrm{dR}}^{p+q}(X;\mathbb C)`)+p('<strong>'+t('注（与 Hodge 分解的关系）。','Remark (relation to Hodge decomposition).')+'</strong> '+t('收敛本身只得到这些商空间。若 X 为紧 Kähler 流形，3.5 进一步证明在第一页退化，从而','Convergence alone gives these quotient spaces. If X is compact Kähler, 3.5 additionally proves degeneration at the first page, giving'))+eq(R`H^q(X,\Omega_X^p)\cong E_1^{p,q}\cong E_\infty^{p,q}\cong\operatorname{Gr}_F^pH_{\mathrm{dR}}^{p+q}(X;\mathbb C)`)+p(t('要得到上同调内部的典范直和分解，还需 3.6–3.7 中由 ∂∂̄-引理给出的典范提升与互补性：','To obtain a canonical direct-sum decomposition inside cohomology, one also needs the canonical lifts and opposed filtrations supplied by the ∂∂̄-lemma in 3.6–3.7:'))+eq(R`H_{\mathrm{dR}}^n(X;\mathbb C)=\bigoplus_{p+q=n}H^{p,q}(X),\qquad H^{p,q}(X)=F^pH^n\cap\overline{F^qH^n}`)+p(t('因此收敛是联系的一部分，但收敛甚至加上退化，都不能单独提供这一典范分裂。','Thus convergence is part of the connection, but even convergence together with degeneration does not by itself provide this canonical splitting.'))},
 {f:[R`H^n:=H_{\mathrm{dR}}^n(X;\mathbb C),\qquad\operatorname{Gr}_F^pH^n=F^pH^n/F^{p+1}H^n`],note:t('这就是 Hodge 滤过。FᵖHⁿ 的类可以用首指标至少为 p 的 d-闭形式表示；E∞ 给出相邻层之商。','This is the Hodge filtration. A class in FᵖHⁿ has a d-closed representative whose first type index is at least p; E∞ identifies the adjacent filtration quotient.'),details:p('<strong>'+t('定义。','Definition.')+'</strong> '+base)+eq(hodgeContent.f[3])+p(t('在 1.12 的上同调诱导滤过中代入上述 Dolbeault 双复形，正好得到此定义。2.9 保证相对于这个指定的滤过收敛。无需先选择直和分裂。','Substituting the Dolbeault double complex into the induced cohomology filtration of 1.12 gives this definition. Theorem 2.9 establishes convergence for precisely this filtration. No splitting is chosen.'))},
 ...splittingExpositions({t,math})
 ];
 const entry=data[page]||data[0];
 return proofPanel({key:'hodge-'+page,title:`3.${page+1} ${t(...hodgeTitles[page])}`,formulas:entry.f,note:entry.note,details:entry.details+p(ref),detailsAreComplete:true,math,language});
}
export function hodgeDiagram({page,label,t}){
 let svg='<svg viewBox="0 0 840 525" role="img" aria-label="Hodge decomposition"><defs><marker id="hodge-tip" viewBox="0 0 8 8" refX="6" refY="4" markerWidth="6" markerHeight="6" orient="auto"><path d="M1 1 L6 4 L1 7" fill="none" stroke="var(--gold)"/></marker></defs>',labels='';
 const box=(x,y,w=148)=>{svg+=`<rect x="${x-w/2}" y="${y-25}" width="${w}" height="50" rx="8" fill="var(--graph-region-fill)" stroke="var(--graph-border)"/>`;};
 if(page<=2){
  for(let p=0;p<3;p++)for(let q=0;q<3;q++){
   const x=205+210*p,y=375-125*q;box(x,y);
   labels+=label(x,y,page===2?R`H^{${q}}(X,\Omega_X^{${p}})`:R`\mathcal A^{${p},${q}}(X)`,145);
   if(page===1){if(p<2){svg+=`<path d="M${x+77},${y} H${x+132}" stroke="var(--gold)" marker-end="url(#hodge-tip)"/>`;labels+=label(x+105,y-23,R`\partial`,50,'gold');}if(q<2){svg+=`<path d="M${x},${y-29} V${y-95}" stroke="var(--gold)" marker-end="url(#hodge-tip)"/>`;labels+=label(x+25,y-62,R`\bar\partial`,50,'gold');}}
  }
  labels+=label(420,page===2?425:460,page===2?R`E_1^{p,q}\Longrightarrow H_{\mathrm{dR}}^{p+q}(X;\mathbb C)`:R`p,q\ge0\quad\text{${t("示意窗口","display window")}}`,760,'gold');
 }else if(page===4){
  for(const [i,r] of ['1','2','\\infty'].entries()){const x=180+i*240;box(x,235,185);labels+=label(x,235,R`E_{${r}}^{p,q}`,180,'gold');if(i<2)labels+=label(x+120,235,R`\cong`,50);}
  labels+=label(420,110,R`X\quad\text{${t("紧 Kähler 流形","compact Kähler")}}`,750,'title')+label(420,355,R`d_r^{p,q}=0\qquad(r\ge1)`,740,'gold');
 }else if(page===5){
  box(235,180,225);box(615,180,225);box(615,330,225);
  labels+=label(235,180,R`E_1^{p,q}`,215,'gold')+label(615,180,R`F^pH^{p+q}`,215)+label(615,330,R`\operatorname{Gr}_F^pH^{p+q}`,215,'gold');
  svg+='<path d="M350 180 H497" fill="none" stroke="var(--gold)" marker-end="url(#hodge-tip)"/><path d="M615 210 V298" fill="none" stroke="var(--gold)" marker-end="url(#hodge-tip)"/><path d="M310 215 L496 306" fill="none" stroke="var(--gold)" marker-end="url(#hodge-tip)"/>';
  labels+=label(425,145,R`s_{p,q}`,90,'gold')+label(405,290,R`\cong`,65,'gold');
  labels+=label(420,425,R`\bigoplus_{p+q=n}E_1^{p,q}\xrightarrow[\sum s_{p,q}]{\sim}H^n`,750);
 }else{
  const terms=page===3?[R`\operatorname{Gr}_F^0H^2`,R`\operatorname{Gr}_F^1H^2`,R`\operatorname{Gr}_F^2H^2`]:[R`H^{0,2}(X)`,R`H^{1,1}(X)`,R`H^{2,0}(X)`];
  terms.forEach((tex,i)=>{const x=185+235*i;box(x,255,190);labels+=label(x,255,tex,185,i?'gold':'');if(i<2)labels+=label(x+117,255,R`\oplus`,35);});
  labels+=label(420,115,page===3?R`\operatorname{Gr}_F H^2`:R`H^2_{\mathrm{dR}}(X;\mathbb C)`,730,'title');
  svg+='<path d="M318 212 H757 V298 H318 Z" fill="none" stroke="var(--gold)" stroke-dasharray="5 5" opacity=".6"/>';
  labels+=label(540,340,page===3?R`\operatorname{Gr}_F(F^1H^2)`:R`F^1H^2=H^{1,1}(X)\oplus H^{2,0}(X)`,570,'gold');
  if(page===6)labels+=label(420,432,R`H^{p,q}=F^pH^{p+q}\cap\overline{F^qH^{p+q}}`,760);
 }
 return svg+'</svg>'+labels;
}
