// A symbolic operations panel: boxes indicate spaces and inclusions, never dimensions.
const R=String.raw;
export const totalDegreeTex=n=>R`C^{${n}}:=\operatorname{Tot}^{${n}}K`;
const pick=(lang,zh,en)=>lang==='en'?en:zh;
export function viewNames(s,lang){const choose=(a,b)=>lang==='en'?b:a;return s.module==='initial'?[]:s.module==='learn'?choose(['E₁','E₂','Eᵣ'],['E₁','E₂','Eᵣ']):s.module==='converge'?choose(['目标滤过','稳定','比较映射','核与同构','⇒ 的含义'],['Target filtration','Stabilization','Comparison','Kernel & isomorphism','Meaning of ⇒']):s.module==='trace'?choose(['代表元','横向像','修正','总微分','d₂','E₃'],['Representative','Horizontal image','Correction','Total differential','d₂','E₃']):Array.from({length:s.example==='d3'?6:5},(_,r)=>`E${r}`);}
export function actionNames(s,lang){const all={initial:[[]],learn:[[['闭链：核','边界：像','取商','同一个类'],['Cocycles: kernel','Boundaries: image','Quotient','Same class']],[['滤过项','下一层','D 保持滤过'],['Filtered piece','Next layer','D preserves F']],[['商空间','投影的核','典范识别'],['Quotient','Projection kernel','Canonical identification']],[['诱导 d₀','E₁'],['Induce d₀','E₁']],[['诱导 d₁','代表元检验','E₂'],['Induce d₁','Representatives','Row cohomology']],[['Zᵣ','Bᵣ','Eᵣ','dᵣ','Eᵣ₊₁'],['Zᵣ','Bᵣ','Eᵣ','dᵣ','Eᵣ₊₁']]],converge:[[['总上同调','诱导滤过','滤过商'],['Total cohomology','Induced filtration','Graded quotient']],[['右端消失','真正闭链','所有总边界'],['Right end vanishes','Actual cocycles','All total boundaries']],[['稳定页','比较映射','同一闭代表元'],['Stable page','Comparison map','Same cocycle']],[['映到零','分解代表元','计算核','商掉核','得到同构'],['Maps to zero','Decompose','Compute kernel','Quotient','Isomorphism']],[['收敛记号','扩张信息'],['Convergence notation','Extension data']]]};const row=all[s.module]?.[s.step];if(!row?.length)return [];return row?.[lang==='en'?1:0]||[];}
export function operationMarkup(s,lang,math){
 const t=(z,e)=>pick(lang,z,e),M=x=>math(x),box=(x,cls='')=>`<div class="space-box ${cls}">${M(x)}</div>`,arrow=x=>`<div class="map-arrow">${M(R`\xrightarrow{${x}}`)}</div>`,row=x=>`<div class="operation-row">${x}</div>`;
 const nested=(outer,inner,small,quotient,focus)=>row(`<div class="space-container">${M(outer)}<div class="subspace ${focus==='kernel'?'chosen':''}">${M(inner)}<div class="boundary-space ${focus==='image'?'chosen':''}">${M(small)}</div></div></div><div class="quotient-operation ${focus==='quotient'?'chosen':''}"><small>${t('中间子空间的商映射','Quotient map on the inner subspace')}</small><div>${M(R`${inner.split(/:?=/)[0]}\xrightarrow{\pi}${quotient.split(/:?=/)[0]}`)}</div><div>${M(R`\ker\pi=${small.split(/:?=/)[0]}`)}</div></div>`);
 const n=s.n,p=s.p,q=n-p,r=Math.max(1,s.r),a=s.module==='initial'?(s.effect==='totalmap'?3:1):s.annotationStep,c=s.effect;let body='',note='';
 if(s.module==='initial'&&!['total','totalmap'].includes(c)){
  if(c==='filtration'){
   body=row(box(`F^{${p}}C^{${n}}:=\\bigoplus_{i\\ge ${p}}K^{i,${n}-i}`,'chosen'))+`<div class="operation-equation">${M(R`F^{p+1}C^n\subseteq F^pC^n`)}</div>`;
  }else if(c==='zeropage'){
   body=row(box(`E_0^{${p},${q}}`)+box(R`\cong`)+box(p<=n?`K^{${p},${q}}`:'0','chosen'))+`<div class="operation-equation">${M(R`E_0^{p,q}:=\operatorname{Gr}_F^pC^{p+q}`)}</div>`;
  }else if(c==='totalsquare'){
   body=`<div class="operation-equation">${M(R`D^2a=\delta_1^2a+(\delta_2\delta_1a+\delta_1\delta_2a)+\delta_2^2a`)}</div><div class="operation-equation">${M(R`\delta_1^2a=0,\quad\delta_2^2a=0,\quad\delta_2\delta_1a=-\delta_1\delta_2a`)}</div>`;
  }else if(c==='square'){
   body=row(box(R`\delta_1^2=0`)+box(R`\delta_2^2=0`));
  }else if(c==='square1'||c==='square2'){
   const h=c==='square1',d=h?1:2,mid=h?'2,1':'1,2',end=h?'3,1':'1,3';
   body=row(box('a\\in K^{1,1}')+arrow(`\\delta_${d}`)+box(`\\delta_${d}a\\in K^{${mid}}`)+arrow(`\\delta_${d}`)+box(`0\\in K^{${end}}`,'chosen'));
   note=t('复合映射为零。终点是零向量；末端空间与两条单独的微分不必为零。','The composite is zero. The endpoint is the zero vector; neither the target space nor either individual map must vanish.');
  }else if(c==='anticommute'){
   body=`<div class="path-comparison"><div>${M(R`K^{1,1}\ni a\xrightarrow{\delta_1}\delta_1a\xrightarrow{\delta_2}\delta_2\delta_1a`)}</div><div>${M(R`K^{1,1}\ni a\xrightarrow{\delta_2}\delta_2a\xrightarrow{\delta_1}\delta_1\delta_2a`)}</div><div class="relation-sum">${M(R`\delta_2\delta_1a+\delta_1\delta_2a=0\in K^{2,2}`)}</div></div>`;
   note=t('取 a∈K¹¹。两条路径的终点空间相同，复合映射互为相反数；不要求各自为零。','Take a∈K¹¹. The two paths reach the same space and their composites are negatives; neither composite is required to vanish.');
  }else if(c==='delta1'||c==='delta2'){
   const d=c==='delta1'?1:2;body=row(box('K^{p,q}')+arrow(`\\delta_${d}`)+box(d===1?'K^{p+1,q}':'K^{p,q+1}','chosen'));
   note=t('箭头表示线性映射；节点表示整个向量空间。','Arrows denote linear maps; nodes denote entire vector spaces.');
  }else{body=row(box(R`K:=\{K^{p,q}\}_{p,q\in\mathbb Z}`)+box(R`K^{p,q}=0\quad(p<0\ \text{or}\ q<0)`));note=t('选择左侧定义。在固定坐标图上加入微分，再单独检验复合关系。','Select a definition to add its maps to the fixed grid and inspect the composite relations.');}
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
   note=t('金色框中的向量投影到第 p 列。蓝色子框是投影的核：这些分量在商中为零，原来的 K 空间仍存在。','Project a vector in the gold region onto column p. The blue subregion is the kernel: its components are zero in the quotient; the original K-spaces still exist.');
  }else if(s.step===3||s.step===4){
   const vertical=s.step===3,d=vertical?'d_0':'d_1',E=vertical?'E_0':'E_1',next=vertical?'E_1':'E_2',incoming=vertical?'p,q-1':'p-1,q',outgoing=vertical?'p,q+1':'p+1,q';
   if(a===1||!vertical&&a===2)body=row(box(`${E}^{${incoming}}`)+arrow(d)+box(`${E}^{p,q}`,'chosen')+arrow(d)+box(`${E}^{${outgoing}}`));
   else body=row(box(vertical?R`E_1^{p,q}\cong H^q(K^{p,\bullet},\delta_2)`:R`E_2^{p,q}:=H^p(E_1^{\bullet,q},d_1)`,'chosen'));
   note=vertical?t('E₀ 上的 d₀ 识别为 δ₂；逐列上同调给出 E₁。','On E₀, d₀ identifies with δ₂; column cohomology gives E₁.'):t('先在 E₁ 上定义 d₁，再取其上同调。取商后的 E₂ 不再连接旧的 d₁；新的微分是 d₂。','Define d₁ on E₁, then take its cohomology. The resulting E₂ nodes are not connected by the old d₁; their new differential is d₂.');
  }else{
   if(a===1)body=row(box(R`a\in F^pC^n`)+arrow('D')+box(R`Da\in F^{p+r}C^{n+1}`,'chosen'))+`<div class="operation-equation">${M(R`Z_r^{p,q}:=\{a\in F^pC^n:Da\in F^{p+r}C^{n+1}\}`)}</div>`;
   if(a===2)body=row(box(R`b\in F^{p-r}C^{n-1}`)+arrow('D')+box(R`Db\in F^pC^n`,'chosen'))+`<div class="operation-equation">${M(R`B_r^{p,q}:=F^pC^n\cap D(F^{p-r}C^{n-1})`)}</div>`;
   if(a===3)body=nested(R`F^pC^n`,R`Z_r^{p,q}`,R`Z_{r-1}^{p+1,q-1}+B_{r-1}^{p,q}`,R`E_r^{p,q}`,'quotient');
   if(a===4)body=row(box(R`[a]_r\in E_r^{p,q}`)+arrow('d_r')+box(R`[Da]_r\in E_r^{p+r,q-r+1}`,'chosen'));
   if(a===5)body=nested(R`E_r^{p,q}`,R`\ker d_r^{p,q}`,R`\operatorname{im}d_r^{p-r,q+r-1}`,R`E_{r+1}^{p,q}`,'quotient');
   note=a<=2?t('这些是总复形中的子空间条件，不是从一个 K 节点到另一个 K 节点的单次微分。n=p+q。','These are subspace conditions in the total complex, not a single differential between two K-nodes. Here n=p+q.'):t('先取代表元的商，再由同一个 D 诱导 dᵣ。图中的箭头位移为 (r,1−r)，总次数增加一。','First quotient representatives, then induce dᵣ using the same D. Its displacement is (r,1−r), raising total degree by one.');
  }
 }else if(s.module==='converge'){
  if(s.step===0){body=a===1?row(box(R`H^n(C^\bullet,D)`,'chosen')):a===3?nested(R`H^n`,R`F^pH^n`,R`F^{p+1}H^n`,R`\operatorname{Gr}_F^pH^n`,'quotient'):row(box(R`a\in F^pC^n\cap\ker D`)+arrow(R`a\mapsto[a]_H`)+box(R`F^pH^n\subseteq H^n`,'chosen'));note=t('取 H(FᵖC)→H(C) 的像：在总上同调中模掉所有总边界，包括从更低滤过来的边界。','Take the image of H(FᵖC)→H(C): in total cohomology, quotient by all total boundaries, including those coming from lower filtration.');}
  if(s.step===1){body=row(box(`a\\in F^{${p}}C^{${n}}`)+arrow('D')+box(`Da\\in F^{${p+r}}C^{${n+1}}${p+r>n+1?'=0':''}`,'chosen'))+`<div class="operation-equation">${M(p+r>n+1?R`Z_r^{p,q}=F^pC^n\cap\ker D`:R`p+r>n+1\ \Longrightarrow\ Z_r^{p,q}=F^pC^n\cap\ker D`)}</div>`;if(a===2)body=row(box(R`a\in Z_r^{p,q}`)+arrow('D')+box(p+r>n+1?'Da=0':R`Da\in F^{p+r}C^{n+1}`,'chosen'));if(a===3)body=row(box(`b\\in F^{${p-r}}C^{${n-1}}${r>=p?`=C^{${n-1}}`:''}`)+arrow('D')+box(R`Db\in F^pC^n`,'chosen'));note=t('调节 r。右边的滤过项消失时，条件成为 Da=0；r≥p 时左边已包含全部来源，Bᵣ 等于 FᵖCⁿ 中的所有总边界。','Adjust r. When the target filtration vanishes, the condition is Da=0. For r≥p, all sources of total boundaries are included, so Bᵣ contains every total boundary in FᵖCⁿ.');}
  if(s.step===2){body=row(box(R`a\in Z_\infty^{p,q}`)+arrow(R`\text{quotient}`)+box(R`[a]_\infty`)+arrow(R`\theta^{p,q}`)+box(R`[a]_H+F^{p+1}H^n`,'chosen'));if(a===1)body=nested(R`F^pC^n`,R`Z_\infty^{p,q}`,R`Z_\infty^{p+1,q-1}+B_\infty^{p,q}`,R`E_\infty^{p,q}`,'quotient');if(a===2)body=row(box(R`E_\infty^{p,q}`)+arrow(R`\theta^{p,q}`)+box(R`\operatorname{Gr}_F^pH^n`,'chosen'));note=t('同一个闭代表元，两个不同的商。总边界先在 Hⁿ 中为零，更高滤过中的闭链再在 Gr 中为零。','One cocycle, two quotients. Total boundaries vanish in Hⁿ; cocycles in the next filtration layer then vanish in Gr.');}
  if(s.step===3){body=row(box(R`a=b+Dc`)+arrow(R`a\mapsto[a]_H+F^{p+1}H^n`)+box('0','chosen'))+`<div class="operation-equation">${M(R`b\in Z_\infty^{p+1,q-1},\quad Dc\in B_\infty^{p,q}`)}</div>`;if(a===1)body=row(box(R`[a]_H\in F^{p+1}H^n`)+arrow(R`\text{in Gr}`)+box('0','chosen'));if(a===3)body=row(box(R`Z_\infty^{p,q}`)+arrow(R`a\mapsto[a]_H+F^{p+1}H^n`)+box(R`\operatorname{Gr}_F^pH^n`))+`<div class="operation-equation">${M(R`\ker=Z_\infty^{p+1,q-1}+B_\infty^{p,q}`)}</div>`;if(a===4)body=nested(R`F^pC^n`,R`Z_\infty^{p,q}`,R`Z_\infty^{p+1,q-1}+B_\infty^{p,q}`,R`E_\infty^{p,q}`,'quotient');if(a===5)body=row(box(R`E_\infty^{p,q}`)+arrow(R`\theta^{p,q}\;\sim`)+box(R`\operatorname{Gr}_F^pH^n`,'chosen'));note=t('映到零恰好等价于这个分解。核是 Z∞ 的下一层加上总边界，正好等于 E∞ 的分母；满射取商即为同构。','Mapping to zero is equivalent to this decomposition. The kernel is the next layer of Z∞ plus total boundaries, exactly the denominator of E∞; the surjection therefore induces an isomorphism.');}
  if(s.step===4){body=nested(R`H^n`,R`F^pH^n`,R`F^{p+1}H^n`,R`E_\infty^{p,n-p}`,'quotient');if(a===1)body=row(box(R`E_\infty^{p,q}\cong\operatorname{Gr}_F^pH^{p+q}`,'chosen'))+`<div class="operation-equation">${M(R`E_r^{p,q}\Longrightarrow H^{p+q}(C,D)`)}</div>`;note=t('⇒ 表示稳定页识别为目标的滤过商；它不是 Eᵣ→H 的线性映射，也不给 Hⁿ 指定典范直和分解。','⇒ denotes identification of the stable page with the target’s filtration quotients. It is neither a map Eᵣ→H nor a specified canonical direct-sum splitting of Hⁿ.');}
 }else{body=s.module==='trace'&&s.step===4?row(box(R`[a_0+c]_2\in E_2^{0,1}`)+arrow('d_2')+box(R`[z]_2\in E_2^{2,0}`)):s.module==='trace'&&s.step===5?row(box(R`E_3^{p,q}=0`)+box(R`H^n(C,D)=0`)):row(box(s.module==='trace'?R`a_0:=b+\lambda y`:R`E_r^{p,q}:=Z_r^{p,q}/(Z_{r-1}^{p+1,q-1}+B_{r-1}^{p,q})`));note=t('例子只在本页切换。点击节点查看精确矩阵与代表元；底部翻页不播放计算过程。','Explore the example locally. Select a node for exact matrices and representatives; the footer does not play the computation.');}
 return `<div class="operation-content">${body}</div>${s.module==='initial'?'':`<p class="operation-note">${note}</p>`}`;
}
