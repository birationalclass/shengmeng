// A symbolic operations panel: boxes indicate spaces and inclusions, never dimensions.
const R=String.raw;
export const totalDegreeTex=n=>R`C^{${n}}:=\operatorname{Tot}^{${n}}K`;
const pick=(lang,zh,en)=>lang==='en'?en:zh;
export function viewNames(s,lang){const choose=(a,b)=>lang==='en'?b:a;return s.module==='initial'?[]:s.module==='learn'?choose(['E₁','E₂','Eᵣ'],['E₁','E₂','Eᵣ']):s.module==='converge'?choose(['目标滤过','稳定','比较映射','核与同构','⇒ 的含义'],['Target filtration','Stabilization','Comparison','Kernel & isomorphism','Meaning of ⇒']):s.module==='trace'?choose(['代表元','横向像','修正','总微分','d₂','E₃'],['Representative','Horizontal image','Correction','Total differential','d₂','E₃']):Array.from({length:s.example==='d3'?6:5},(_,r)=>`E${r}`);}
export function actionNames(s,lang){if(s.module==='converge')return [];const all={initial:[[]],learn:[[['闭链：核','边界：像','取商','同一个类'],['Cocycles: kernel','Boundaries: image','Quotient','Same class']],[['滤过项','下一层','D 保持滤过'],['Filtered piece','Next layer','D preserves F']],[['商空间','投影的核','典范识别'],['Quotient','Projection kernel','Canonical identification']],[['E₀','d₀'],['E₀','d₀']],[['E₁','d₁','代表元'],['E₁','d₁','Representatives']],[['Zᵣ','Bᵣ','Eᵣ','dᵣ'],['Zᵣ','Bᵣ','Eᵣ','dᵣ']]],converge:[[['总上同调','诱导滤过','滤过商'],['Total cohomology','Induced filtration','Graded quotient']],[['右端消失','真正闭链','所有总边界'],['Right end vanishes','Actual cocycles','All total boundaries']],[['稳定页','比较映射','同一闭代表元'],['Stable page','Comparison map','Same cocycle']],[['映到零','分解代表元','计算核','商掉核','得到同构'],['Maps to zero','Decompose','Compute kernel','Quotient','Isomorphism']],[['收敛记号','扩张信息'],['Convergence notation','Extension data']]]};const row=all[s.module]?.[s.step];if(!row?.length)return [];return row?.[lang==='en'?1:0]||[];}
export function operationMarkup(s,lang,math){
 const t=(z,e)=>pick(lang,z,e),M=x=>math(x),box=(x,cls='')=>`<div class="space-box ${cls}">${M(x)}</div>`,arrow=x=>`<div class="map-arrow">${M(R`\xrightarrow{${x}}`)}</div>`,row=x=>`<div class="operation-row">${x}</div>`;
 const nested=(outer,inner,small,quotient,focus)=>row(`<div class="space-container">${M(outer)}<div class="subspace ${focus==='kernel'?'chosen':''}">${M(inner)}<div class="boundary-space ${focus==='image'?'chosen':''}">${M(small)}</div></div></div><div class="quotient-operation ${focus==='quotient'?'chosen':''}"><small>${t('中间子空间的商映射','Quotient map on the inner subspace')}</small><div>${M(R`${inner.split(/:?=/)[0]}\xrightarrow{\pi}${quotient.split(/:?=/)[0]}`)}</div><div>${M(R`\ker\pi=${small.split(/:?=/)[0]}`)}</div></div>`);
 const n=s.n,p=s.p,q=n-p,r=Math.max(1,s.r),a=s.module==='initial'?(s.effect==='totalmap'?3:1):s.annotationStep,c=s.effect;let body='',note='';
 if(s.module==='initial'&&!['total','totalmap'].includes(c)){
  if(c==='totalcohom'){
   body=row(box(n===0?'0':`C^{${n-1}}`)+arrow('D')+box(`C^{${n}}`,'chosen')+arrow('D')+box(`C^{${n+1}}`))+`<div class="operation-equation">${M(R`\operatorname{im}(D:C^{n-1}\to C^n)\subseteq\ker(D:C^n\to C^{n+1})`)}</div>`;
   body+=`<div class="operation-equation">${M(R`[a]_H:=a+\operatorname{im}(D:C^{n-1}\to C^n),\quad Da=0`)}</div>`;
   note=t(`由 ${M('D^2=0')}，这个商空间有定义。${M(R`H^n(C^\bullet,D)`)} 是最终要计算的总上同调，涉及整条总次数对角线，不属于单个 ${M(R`K^{p,q}`)}。`,`${M('D^2=0')} makes this quotient well-defined. The target ${M(R`H^n(C^\bullet,D)`)} is total cohomology: it involves the whole total-degree diagonal, not a single ${M(R`K^{p,q}`)} term.`);
  }else if(c==='filteredmap'){
   body=row(box(`F^{${p}}C^{${n}}`,'source-space')+arrow('D')+box(`F^{${p}}C^{${n+1}}`,'target-space'))+`<div class="operation-equation">${M(R`a=\sum_{i\ge ${p}}a_i,\quad a_i\in K^{i,${n}-i}`)}</div><div class="operation-equation">${M(R`(Da)_j=\delta_1a_{j-1}+\delta_2a_j=0\quad(j<${p})`)}</div><div class="operation-equation">${M(R`D(F^{${p}}C^{${n}})\subseteq F^{${p}}C^{${n+1}}`)}</div>`;
  }else if(c==='filtration'){
   body=row(box(`F^{${p}}C^{${n}}:=\\bigoplus_{i\\ge ${p}}K^{i,${n}-i}`,'chosen'))+`<div class="operation-equation">${M(R`F^{p+1}C^n\subseteq F^pC^n`)}</div>`;
  }else if(c==='zeropage'){
   body=row(box(`E_0^{${p},${q}}`)+box(R`\cong`)+box(p<=n?`K^{${p},${q}}`:'0','chosen'))+`<div class="operation-equation">${M(R`E_0^{p,q}:=\operatorname{Gr}_F^pC^{p+q}`)}</div>`;
  }else if(c==='totalsquare'){
   body=`<div class="operation-equation">${M(R`\begin{aligned}D^2&=(\delta_1+\delta_2)^2\\&=\delta_1^2+(\delta_1\delta_2+\delta_2\delta_1)+\delta_2^2=0.\end{aligned}`)}</div>`;
   note=t(`这保证 ${M(R`(C^\bullet,D)`)} 构成上链复形，从而可以定义其上同调 ${M(R`H^n(C^\bullet,D)`)}。`,`Thus ${M(R`(C^\bullet,D)`)} is a cochain complex, and its cohomology ${M(R`H^n(C^\bullet,D)`)} is defined.`);
  }else if(['square','square1','square2'].includes(c)){
   body=`<p class="operation-description">${t(`${M(R`\delta_1^2=0`)} 省略了双次数指标。两个 ${M(R`\delta_1`)} 分别是 ${M(R`\delta_1^{p,q}`)} 与 ${M(R`\delta_1^{p+1,q}`)}，是定义域不同的分量映射。准确地写，横向与纵向的平方零关系为：`,`${M(R`\delta_1^2=0`)} suppresses the bidegrees. Its two occurrences of ${M(R`\delta_1`)} are ${M(R`\delta_1^{p,q}`)} and ${M(R`\delta_1^{p+1,q}`)}, component maps with different domains. The horizontal and vertical square-zero relations are:`)}</p>`+
    `<div class="operation-equation">${M(R`\begin{aligned}\delta_1^{p+1,q}\circ\delta_1^{p,q}&=0,\\\delta_2^{p,q+1}\circ\delta_2^{p,q}&=0.\end{aligned}`)}</div>`;
   note=t(`这里分别是 ${M(R`K^{p,q}\to K^{p+2,q}`)} 与 ${M(R`K^{p,q}\to K^{p,q+2}`)} 的零映射。因此每行、每列都是上链复形，可分别取上同调。`,`These are the zero maps ${M(R`K^{p,q}\to K^{p+2,q}`)} and ${M(R`K^{p,q}\to K^{p,q+2}`)}, respectively. Thus each row and column is a cochain complex, with its own cohomology.`);
  }else if(c==='anticommute'){
   body=`<p class="operation-description">${t(`${M(R`\delta_1,\delta_2`)} 是一族分量映射的简写；上标记录定义域的双次数：`,`${M(R`\delta_1,\delta_2`)} abbreviate families of component maps; the superscripts record the bidegree of the domain:`)}</p>`+
    `<div class="operation-equation">${M(R`\begin{aligned}\delta_1^{p,q}&:K^{p,q}\longrightarrow K^{p+1,q}\\\delta_2^{p,q}&:K^{p,q}\longrightarrow K^{p,q+1}\end{aligned}`)}</div>`+
    `<div class="operation-equation">${M(R`\delta_1^{p,q+1}\circ\delta_2^{p,q}+\delta_2^{p+1,q}\circ\delta_1^{p,q}=0`)}</div>`;
   note=t(`两个 ${M(R`\delta_1`)} 分别是 ${M(R`\delta_1^{p,q+1}`)} 与 ${M(R`\delta_1^{p,q}`)}，并非同一个分量映射。两项复合均为 ${M(R`K^{p,q}\to K^{p+1,q+1}`)}，相加为零映射。图中取 ${M(R`p=q=1`)}。`,`The two occurrences of ${M(R`\delta_1`)} mean ${M(R`\delta_1^{p,q+1}`)} and ${M(R`\delta_1^{p,q}`)}, different component maps. Both composites are maps ${M(R`K^{p,q}\to K^{p+1,q+1}`)} and sum to the zero map. The diagram uses ${M(R`p=q=1`)}.`);
  }else if(c==='delta1'||c==='delta2'){
   const d=c==='delta1'?1:2;body=row(box('K^{p,q}')+arrow(`\\delta_${d}`)+box(d===1?'K^{p+1,q}':'K^{p,q+1}','chosen'));
   note=t(`${M(`\\delta_${d}`)} 是线性映射。`, `${M(`\\delta_${d}`)} is a linear map.`);
  }else{
   body=`<p class="operation-description">${t(`每个 ${M(R`K^{p,q}`)} 是向量空间。`, `Each ${M(R`K^{p,q}`)} is a vector space.`)}</p><p class="operation-description">${t('本笔记采用第一象限约定：','In this notebook we use the first-quadrant convention:')}</p><div class="operation-equation">${M(R`K^{p,q}=0\qquad(p<0\ \text{or}\ q<0)`)}</div>`;
  }
 }else if(s.module==='initial'){
  const factors=Array.from({length:n+1},(_,i)=>`K^{${i},${n-i}}`);
  if(a===1)body=`<div class="operation-equation">${M(totalDegreeTex(n))}</div>`+row(`<span>${M('=')}</span><div class="direct-sum-group">${factors.map(x=>`<span>${M(x)}</span>`).join(`<span class="sum-sign">${M('\\oplus')}</span>`)}</div>`);
  else if(a===2)body=row(box(`a_{i,j}\\in K^{i,j}`)+arrow('D')+box(R`\delta_1a_{i,j}+\delta_2a_{i,j}\in C^{i+j+1}`,'chosen'));
  else body=row(box(totalDegreeTex(n),'source-space')+arrow('D')+box(totalDegreeTex(n+1),'target-space'))+`<div class="operation-equation">${M(R`(Da)_{i,j}=\delta_1a_{i-1,j}+\delta_2a_{i,j-1}`)}</div>`;
  note=a===1?t('斜虚框圈出全部直和因子，整体记作 Cⁿ；它不是新加的一个 K 节点。','The slanted dashed box groups all direct-sum factors as Cⁿ. It is not an extra K-node.'):t('金色框是定义域，蓝色框是下一总次数。D 将每个分量的横向像与纵向像相加；指标为负的分量取零。','The gold box is the domain; the blue box is the next total degree. D adds the horizontal and vertical images of each component; negative-index components are zero.');
 }else if(s.module==='learn'){
  if(s.step===0){
   body=nested(`C^{${n}}`,`Z^{${n}}:=\\ker D`,`B^{${n}}:=\\operatorname{im}D`,`H^{${n}}:=Z^{${n}}/B^{${n}}`,a===1?'kernel':a===2?'image':'quotient');
   if(a===4)body=row(box(R`a\in Z^n`)+arrow(R`\pi`)+box(R`[a]_H:=a+B^n`,'chosen'))+`<div class="operation-equation">${M(R`a'=a+Db\ \Longrightarrow\ [a']_H=[a]_H`)}</div>`;
   note=t('此处 ker D 的定义域是 Cⁿ，im D 来自 Cⁿ⁻¹。D²=0 给出 Bⁿ⊆Zⁿ。区域只表示包含关系，不表示维数或补空间。','Here ker D has domain Cⁿ, and im D comes from Cⁿ⁻¹. D²=0 gives Bⁿ⊆Zⁿ. Regions show inclusions, not dimensions or complements.');
  }else if(s.step===1){
   body=a===3?row(box(`F^{${p}}C^{${n}}`)+arrow('D')+box(`F^{${p}}C^{${n+1}}`,'target-space')):row(`<div class="space-container">${M(`C^{${n}}`)}<div class="subspace">${M(`F^{${p}}C^{${n}}`)}<div class="boundary-space ${a===2?'chosen':''}">${M(`F^{${p+1}}C^{${n}}`)}</div></div></div>`);
   note=t('p 控制同一条对角线的起点；p>n 时为空。D 保持列滤过，但将总次数从 n 提高到 n+1。','p controls the starting point on the same diagonal; p>n gives zero. D preserves the column filtration while raising total degree by one.');
  }else if(s.step===2){
   body=row(box(`F^{${p}}C^{${n}}`)+arrow(R`\mathrm{pr}_{${p}}`)+box(p<=n?`K^{${p},${q}}`:'0','chosen'))+`<div class="operation-equation">${M(R`\ker\mathrm{pr}_p=F^{p+1}C^n,\qquad E_0^{p,n-p}:=F^pC^n/F^{p+1}C^n\cong K^{p,n-p}`)}</div>`;
   note=t('取第 p 列分量；核为下一层滤过。','Project to column p; the kernel is the next filtration layer.');
  }else if(s.step===3||s.step===4){
   const vertical=s.step===3,d=vertical?'d_0':'d_1',E=vertical?'E_0':'E_1',next=vertical?'E_1':'E_2',incoming=vertical?'p,q-1':'p-1,q',outgoing=vertical?'p,q+1':'p+1,q';
   if(a===1||!vertical&&a===2)body=row(box(`${E}^{${incoming}}`)+arrow(d)+box(`${E}^{p,q}`,'chosen')+arrow(d)+box(`${E}^{${outgoing}}`));
   else body=row(box(vertical?R`E_1^{p,q}\cong H^q(K^{p,\bullet},\delta_2)`:R`E_2^{p,q}:=H^p(E_1^{\bullet,q},d_1)`,'chosen'));
   note=vertical?t('E₀ 上的 d₀ 识别为 δ₂；逐列上同调给出 E₁。','On E₀, d₀ identifies with δ₂; column cohomology gives E₁.'):t('对 d₁ 取上同调得到 E₂，其微分为 d₂。','Cohomology of d₁ gives E₂, whose differential is d₂.');
  }else{
   if(a===1)body=row(box(R`a\in F^pC^n`)+arrow('D')+box(R`Da\in F^{p+r}C^{n+1}`,'chosen'))+`<div class="operation-equation">${M(R`Z_r^{p,q}:=\{a\in F^pC^n:Da\in F^{p+r}C^{n+1}\}`)}</div>`;
   if(a===2)body=row(box(R`b\in F^{p-r}C^{n-1}`)+arrow('D')+box(R`Db\in F^pC^n`,'chosen'))+`<div class="operation-equation">${M(R`B_r^{p,q}:=F^pC^n\cap D(F^{p-r}C^{n-1})`)}</div>`;
   if(a===3)body=nested(R`F^pC^n`,R`Z_r^{p,q}`,R`Z_{r-1}^{p+1,q-1}+B_{r-1}^{p,q}`,R`E_r^{p,q}`,'quotient');
   if(a===4)body=row(box(R`[a]_r\in E_r^{p,q}`)+arrow('d_r')+box(R`[Da]_r\in E_r^{p+r,q-r+1}`,'chosen'));
   if(a===5)body=nested(R`E_r^{p,q}`,R`\ker d_r^{p,q}`,R`\operatorname{im}d_r^{p-r,q+r-1}`,R`E_{r+1}^{p,q}`,'quotient');
   note=a<=2?t('这些是总复形中的子空间；n=p+q。','These are subspaces of the total complex; n=p+q.'):t('D 诱导 dᵣ，其双次数为 (r,1−r)。','D induces dᵣ, of bidegree (r,1−r).');
  }
 }else if(s.module==='converge'){body='';
 }else{body=s.module==='trace'&&s.step===4?row(box(R`[a_0+c]_2\in E_2^{0,1}`)+arrow('d_2')+box(R`[z]_2\in E_2^{2,0}`)):s.module==='trace'&&s.step===5?row(box(R`E_3^{p,q}=0`)+box(R`H^n(C,D)=0`)):row(box(s.module==='trace'?R`a_0:=b+\lambda y`:R`E_r^{p,q}:=Z_r^{p,q}/(Z_{r-1}^{p+1,q-1}+B_{r-1}^{p,q})`));note=t('','');}
 if(s.module==='initial'&&c==='totalmap'){
  const i=Math.floor(n/2),j=n-i;
  body=`<div class="operation-equation">${M(R`a\in K^{${i},${j}}\subseteq C^{${n}}`)}</div>`+body+
   `<div class="operation-equation">${M(R`Da=\delta_1a+\delta_2a\in C^{${n+1}}`)}</div>`;
 }
 if(n===4&&s.module==='initial'&&['totalmap','filteredmap'].includes(c))body+=`<p class="operation-note">${t(`蓝色区域还包括窗口外的 ${M(R`K^{0,5},\ K^{5,0}`)}。`,`The blue region also includes ${M(R`K^{0,5},\ K^{5,0}`)} beyond the displayed window.`)}</p>`;
 return `<div class="operation-content">${body}</div>${note&&(s.module!=='initial'||['delta1','delta2','square','square1','square2','anticommute','totalsquare','totalcohom'].includes(c))?`<p class="operation-note">${note}</p>`:''}`;
}
