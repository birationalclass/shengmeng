const R=String.raw;
export const firstQuadrantTitle=['第一象限收敛性','First-quadrant convergence'];
export const firstQuadrantFormula=R`\begin{gathered}K^{i,j}=0\quad(i<0\text{ or }j<0)\\[.4em]E_r^{p,q}\Longrightarrow H^{p+q}(C^\bullet,D)\\[.4em]E_\infty^{p,q}\cong\frac{F^pH^{p+q}}{F^{p+1}H^{p+q}}\end{gathered}`;
export function firstQuadrantContent({math,t}){
 const eq=x=>`<div class="operation-equation">${math(x,true)}</div>`,para=x=>`<p>${x}</p>`;
 const mc='https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/McCleary-UGSS.pdf';
 const references=`<a href="${mc}#page=62" target="_blank" rel="noopener">McCleary, A User’s Guide to Spectral Sequences, 2nd ed., Theorem 2.15, p. 48</a> · <a href="${mc}#page=47" target="_blank" rel="noopener">Theorem 2.6, pp. 33–34</a>`;
 const assumptions=t(`设 ${math(R`(K^{\bullet,\bullet},\delta_1,\delta_2)`)} 是向量空间（或同一环上的模）的第一象限双复形。本文使用 McCleary 定理 2.15 的第一种（列滤过）谱序列，记号约定为 ${math(R`F=F_I,\ E_r={}^{I}E_r`)}，采用 ${math(R`\delta_1\delta_2+\delta_2\delta_1=0`)} 的约定。令总复形及其列滤过为`,`Let ${math(R`(K^{\bullet,\bullet},\delta_1,\delta_2)`)} be a first-quadrant double complex of vector spaces (or modules over a fixed ring). We use the first (column-filtration) spectral sequence of McCleary’s Theorem 2.15, writing ${math(R`F=F_I,\ E_r={}^{I}E_r`)}. Assume ${math(R`\delta_1\delta_2+\delta_2\delta_1=0`)}. Define its total complex and column filtration by`);
 const hypothesisFormulas=[R`K^{i,j}=0\quad(i<0\text{ or }j<0)`,R`C^n:=\bigoplus_{i+j=n}K^{i,j},\qquad D:=\delta_1+\delta_2`,R`F^pC^n:=\bigoplus_{\substack{i+j=n\\i\ge p}}K^{i,j}`,R`H^n:=H^n(C^\bullet,D),\qquad F^pH^n:=\operatorname{im}\!\left(H^n(F^pC^\bullet,D|_{F^pC^\bullet})\xrightarrow{H^n(\iota_p)} H^n(C^\bullet,D)\right)`];
 const conclusionLead=t('则列滤过的谱序列按照 2.12 的约定，相对于上述诱导滤过收敛到总上同调，具体有以下有限滤过及自然同构。行滤过的谱序列同样收敛到总上同调，使用其自身诱导的滤过。','Then the column-filtration spectral sequence converges to total cohomology with respect to the specified induced filtration, in the sense of 2.12, with the following finite filtration and natural isomorphisms. The row-filtration spectral sequence also converges to total cohomology, with its own induced filtration.');
 const conclusions=[R`H^n=F^0H^n\supseteq\cdots\supseteq F^{n+1}H^n=0\qquad(n\ge0)`,R`E_r^{p,q}\Longrightarrow H^{p+q}(C^\bullet,D)`,R`E_\infty^{p,q}\xrightarrow{\sim}\frac{F^pH^{p+q}}{F^{p+1}H^{p+q}}\qquad(p,q\ge0)`];
 const detail=para(t('我们先验证列滤过的逐次数有限性。第一象限条件给出','We first verify that the column filtration is finite in each degree. The first-quadrant condition gives'))+
 eq(R`C^n=\bigoplus_{i=0}^{n}K^{i,n-i},\qquad F^0C^n=C^n,\qquad F^{n+1}C^n=0`)+
 para(t(`此外 ${math(R`D(F^pC^n)\subseteq F^pC^{n+1}`)}。下面直接使用前面定义的诱导滤过，构造 2.12 要求的自然同构并验证端点。`,`Moreover, ${math(R`D(F^pC^n)\subseteq F^pC^{n+1}`)}. We now use the previously defined induced filtration to construct the natural isomorphism required by 2.12 and verify its endpoints.`))+
 eq(R`n:=p+q,\qquad Z^n:=\ker D^n,\qquad B^n:=\operatorname{im}D^{n-1}`)+
 para(t('固定双次数，取足够大的页数。则','Fix a bidegree and take a sufficiently large page number. Then'))+
 eq(R`r>\max\{p,q+1\}\quad\Longrightarrow\quad F^{p+r}C^{n+1}=0,\qquad F^{p-r+1}C^{n-1}=C^{n-1}`)+
 eq(R`Z_r^{p,q}=F^pC^n\cap Z^n,\qquad Z_{r-1}^{p+1,q-1}=F^{p+1}C^n\cap Z^n`)+
 eq(R`B_{r-1}^{p,q}=F^pC^n\cap B^n`)+
 para(t('代入2.1的商空间定义，得到稳定商','Substituting into the quotient definition in 2.1 gives the stable quotient'))+
 eq(R`E_\infty^{p,q}\cong E_r^{p,q}=\frac{F^pC^n\cap Z^n}{(F^{p+1}C^n\cap Z^n)+(F^pC^n\cap B^n)}`)+
 para(t('构造线性映射','We construct the linear map'))+
 eq(R`\begin{aligned}\theta:F^pC^n\cap Z^n&\longrightarrow F^pH^n/F^{p+1}H^n\\a&\longmapsto[a]_H+F^{p+1}H^n.\end{aligned}`)+
 para(t('由诱导滤过的定义，该映射满射。其核由以下等价关系确定：','The definition of the induced filtration makes this map surjective. Its kernel is determined by'))+
 eq(R`\begin{aligned}\theta(a)=0&\iff [a]_H=[z]_H\ \text{for some }z\in F^{p+1}C^n\cap Z^n\\&\iff a=z+b,\quad z\in F^{p+1}C^n\cap Z^n,\ b\in F^pC^n\cap B^n.\end{aligned}`)+
 eq(R`\ker\theta=(F^{p+1}C^n\cap Z^n)+(F^pC^n\cap B^n)`)+
 para(t('因此第一同构定理给出','Hence the first isomorphism theorem gives'))+
 eq(R`E_\infty^{p,q}\xrightarrow{\sim}F^pH^n/F^{p+1}H^n,\qquad[a]_\infty\longmapsto[a]_H+F^{p+1}H^n`)+
 para(t('上同调滤过的端点直接来自复形滤过：','The endpoints of the cohomology filtration follow directly from those of the complex filtration:'))+
 eq(R`F^0H^n=H^n,\qquad F^{n+1}H^n=\operatorname{im}\!\left(H^n(F^{n+1}C^\bullet)\to H^n(C^\bullet)\right)=0`)+
 para(t(`最后一个等式使用 ${math(R`F^{n+1}C^n=0`)}。行滤过 ${math(R`G^pC^n:=\bigoplus_{i+j=n,\,j\ge p}K^{i,j}`)} 对应 McCleary 的第二种谱序列，同样逐次数有限，重复上述论证即可。这里无需各项有限维；也不要求整个双复形只有有限多个非零项。`,`The last equality uses ${math(R`F^{n+1}C^n=0`)}. The row filtration ${math(R`G^pC^n:=\bigoplus_{i+j=n,\,j\ge p}K^{i,j}`)} gives McCleary’s second spectral sequence; it is likewise finite in each degree, so the same argument applies. Neither finite-dimensional terms nor finitely many nonzero terms in the entire double complex are required.`))+
 para(t(`<strong>注。</strong> McCleary 定理 2.15 给出两条谱序列。本文使用第一种，即列滤过谱序列：`,`<strong>Remark.</strong> McCleary’s Theorem 2.15 gives two spectral sequences. We use the first, namely the column-filtration spectral sequence:`))+
 eq(R`F^pC^n=F_I^pC^n=\bigoplus_{\substack{i+j=n\\i\ge p}}K^{i,j},\qquad E_r^{p,q}={}^{I}E_r^{p,q}`)+
 eq(R`{}^{I}E_1^{p,q}\cong H^q(K^{p,\bullet},\delta_2)`)+
 para(t(`因此先沿纵向 ${math(R`\delta_2`)} 取上同调，再由横向 ${math(R`\delta_1`)} 诱导第一页微分。第二种 ${math(R`{}^{II}E_r`)} 则使用行滤过`,`Thus one first takes vertical cohomology with ${math(R`\delta_2`)}, and the horizontal differential ${math(R`\delta_1`)} induces the first-page differential. The second sequence ${math(R`{}^{II}E_r`)} instead uses the row filtration`))+
 eq(R`F_{II}^pC^n:=\bigoplus_{\substack{i+j=n\\j\ge p}}K^{i,j}`)+
 para(t('其取上同调的次序是先横后纵。两者都收敛到同一个总上同调，但在该上同调上诱导的滤过一般不同；本证明中的 F 始终指列滤过及其在上同调上的诱导滤过。','Its cohomology order is horizontal first, then vertical. Both converge to the same total cohomology, but their induced filtrations on it generally differ. Throughout this proof, F denotes the column filtration and its induced filtration on cohomology.'))+
 para(t(`<strong>关于收敛定义的约定。</strong> McCleary 定义 2.4 只要求目标上存在某个滤过，使稳定项同构于其关联分次。本文 2.12 则固定 2.11 的诱导滤过，并要求上述由闭代表元给出的自然同构；这是一项针对本文双复形构造的具体约定，不应视为 McCleary 定义 2.4 的原文，也不另称为“强收敛”。`,`<strong>Convention on convergence.</strong> McCleary’s Definition 2.4 requires the existence of a filtration on the target whose associated graded is isomorphic to the limit term. Our 2.12 fixes the induced filtration from 2.11 and requires the natural isomorphism on cocycle representatives above. This is a convention for our double-complex construction, not the literal statement of Definition 2.4, and we do not introduce the term “strong convergence” for it.`))+
 para(t('这一更具体的结论确实由 McCleary 的证明给出：他在定理 2.6 前定义上同调滤过为包含映射诱导的像，定理 2.6 及其证明使用该滤过；定理 2.15 对列滤过和行滤过分别应用 2.6。因此引用 2.15 时，可以取各自的诱导滤过，而无需另行选择滤过。这并不声称满足抽象定义 2.4 的滤过唯一。','McCleary’s proof does give this more specific conclusion: immediately before Theorem 2.6, he defines the cohomology filtration as the image of the map induced by inclusion. Theorem 2.6 and its proof use that filtration, and Theorem 2.15 applies 2.6 separately to the column and row filtrations. Thus each sequence converges with respect to its own induced filtration, with no further choice. This does not assert uniqueness among all filtrations satisfying the abstract Definition 2.4.'))+
 para(references);
 return {assumptions,hypothesisFormulas,conclusionLead,conclusions,detail,
 f:[R`F^0C^n=C^n,\qquad F^{n+1}C^n=0`,R`E_\infty^{p,q}\cong F^pH^{p+q}/F^{p+1}H^{p+q}`],
 note:t(`本文采用 McCleary 的列滤过谱序列 ${math(R`E_r={}^{I}E_r`)}。第一象限使每条总次数对角线有限，因此自动收敛到总上同调。`,`We use McCleary’s column-filtration spectral sequence ${math(R`E_r={}^{I}E_r`)}. Each total-degree diagonal is finite, giving convergence to total cohomology.`)+`<br>${references}`};
}
