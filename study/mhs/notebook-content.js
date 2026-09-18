import {chapters as original,ui} from './content.js?v=1';
export {ui};
const R=String.raw;
export function notation(tex,context=''){
 let s=tex.replace(/(?<![A-Za-z\\])F(?![A-Za-z])/g,R`F_{\mathrm{Hdg}}`)
 .replace(/L(\^(?:\{[^}]+\}|[a-z0-9]))C/g,'F$1C')
 .replace(/\bTh\b/g,R`T\delta_1`).replace(/\bhT\b/g,R`\delta_1T`).replace(/\bTv\b/g,R`T\delta_2`).replace(/\bvT\b/g,R`\delta_2T`)
 .replace(/\bhv\b/g,R`\delta_1\delta_2`).replace(/\bvh\b/g,R`\delta_2\delta_1`)
 .replace(/\bha_/g,R`\delta_1a_`).replace(/\bva_/g,R`\delta_2a_`)
 .replace(/\bh\b/g,R`\delta_1`).replace(/\bv\b/g,R`\delta_2`)
 .replace(/H\^n\(C(?:,D)?\)/g,R`H^n(C^\bullet,D)`)
 .replace(/H\^n\(L\^pC\)/g,R`H^n(F^pC^\bullet,D_p)`)
 .replace(/H\^n\(F\^pC\)/g,R`H^n(F^pC^\bullet,D_p)`);
 if(context==='convergence')s=s.replace(/\bL/g,'F').replace(/_L/g,'_F');
 return s;
}
const prose=(text,id)=>text.replace(/\$([^$]+)\$/g,(_,t)=>'$'+notation(t,id)+'$');
export const chapters=original.map(c=>({...c,formulas:c.formulas.map(x=>notation(x,c.id)),intro:c.intro?.map(x=>prose(x,c.id)),proof:c.proof.map(p=>({...p,formulas:p.formulas.map(x=>notation(x,c.id)),text:p.text.map(x=>prose(x,c.id))}))}));
const by=id=>chapters.find(c=>c.id===id);
by('goal').no='0.1';
by('goal').tag=['核心结论 · 收敛、退化与自然性','Main result · Convergence, degeneration and naturality'];
by('goal').proof[1].formulas=[R`(X_\bullet,f_\bullet)\longmapsto(C^\bullet,D,F,T)`,R`E_2^{p,q}\cong E_\infty^{p,q}\cong\operatorname{Gr}_F^pH^{p+q}(C^\bullet,D)`];
by('complex').proof[1].text=[R`纵向微分 $\delta_2$ 已含 $(-1)^p$，因此 $D=\delta_1+\delta_2$，与谱序列课件采用完全相同的反交换约定。`,R`The vertical differential $\delta_2$ includes $(-1)^p$, so $D=\delta_1+\delta_2$, exactly the anticommuting convention of the spectral-sequence course.`];
by('filtrations').title=['诱导滤过与权重','Induced filtration and weights'];
by('filtrations').formulas=[R`F^pC^n:=\bigoplus_{i\ge p}K^{i,n-i}`,R`F^pH^n(C^\bullet,D):=\operatorname{im}H^n(\iota_p)`,R`L^pH^n(X_\bullet,\mathbb Q):=F^pH^n(C^\bullet,D)`,R`W_wH^n:=L^{n-w}H^n`];
by('filtrations').intro=[R`$F$ 用于总复形及其上同调；在 $H^n(X_\bullet,\mathbb Q)$ 上把对应滤过记为 $L$。`,R`Use $F$ for the total complex and its cohomology; denote its transport to $H^n(X_\bullet,\mathbb Q)$ by $L$.`];
by('filtrations').proof[0].formulas=[R`\iota_p:(F^pC^\bullet,D_p)\hookrightarrow(C^\bullet,D)`,R`H^n(\iota_p):[a]_{D_p}\longmapsto[a]_D`,R`D_p=D|_{F^pC^\bullet},\qquad D(F^pC^n)\subseteq F^pC^{n+1}`];
by('hodge').intro=[R`$W$ 是有理空间上的递增滤过；$F_{\mathrm{Hdg}}$ 是复化空间上的 Hodge 滤过，勿与列滤过 $F$ 混淆。`,R`The increasing filtration $W$ is rational; the Hodge filtration $F_{\mathrm{Hdg}}$ is on the complexification, distinct from the column filtration $F$.`];
by('hodge').proof.unshift({title:['Hodge 滤过的形式模型','The form model for the Hodge filtration'],formulas:[R`\mathcal B^m=\bigoplus_{p+a+b=m}\mathcal A^{a,b}(X_p)`,R`D_{\mathcal B}=\delta_1+(-1)^p(\partial+\bar\partial)`,R`F_{\mathrm{Hdg}}^\ell\mathcal B^m=\bigoplus_{\substack{p+a+b=m\\a\ge\ell}}\mathcal A^{a,b}(X_p)`],text:[R`由自然 de Rham 比较把该子复形诱导的滤过传到 $H^n(X_\bullet,\mathbb C)$。`,R`Natural de Rham comparison transports the induced filtration of this subcomplex to $H^n(X_\bullet,\mathbb C)$.`]});
by('pages').proof[3].formulas=[R`Z_r^{p,q}:=F^pC^n\cap D^{-1}(F^{p+r}C^{n+1})`,R`B_r^{p,q}:=F^pC^n\cap D(F^{p-r}C^{n-1})`,R`E_r^{p,q}:=\frac{Z_r^{p,q}}{Z_{r-1}^{p+1,q-1}+B_{r-1}^{p,q}}`,R`d_r^{p,q}:E_r^{p,q}\to E_r^{p+r,q-r+1},\quad[a]_r\mapsto[Da]_r`];
by('pages').proof[3].text=[R`这里 $n=p+q$，页指标 $r\ge0$；辅助空间也按同一公式定义负下标。与谱序列课件一致，$E_{r+1}\cong H(E_r,d_r)$ 是性质。$T_r[a]_r=[Ta]_r$，由 $TD=DT$ 得到微分的交换关系。`,R`Here $n=p+q$ and $r\ge0$; auxiliary spaces use the same formulas also for negative subscripts. As in the spectral-sequence course, $E_{r+1}\cong H(E_r,d_r)$ is a property. The formula $T_r[a]_r=[Ta]_r$ and $TD=DT$ give commutation with the differentials.`];
by('convergence').intro=[R`第一象限保证逐次有限滤过。这一步尚不使用 MHS，也不使用 $E_2$ 退化。`,R`The first quadrant makes the filtration finite in each degree. This step uses neither MHS nor degeneration at $E_2$.`];
by('convergence').formulas=[R`H^n(C^\bullet,D)=F^0H^n\supseteq\cdots\supseteq F^{n+1}H^n=0`,R`E_\infty^{p,q}\cong\operatorname{Gr}_F^pH^n(C^\bullet,D)`,R`\rho_{p,q}:\operatorname{Gr}_L^pH^n(X_\bullet,\mathbb Q)\xrightarrow{\sim}E_\infty^{p,q}`,R`[a]_D+L^{p+1}H^n\longmapsto[a]_\infty`];
by('equivariance').tag=['收敛同构与退化同构的复合','Compose convergence and degeneration'];
const pages={goal:5,simplicial:1,complex:1,filtrations:1,hodge:4,action:5,pages:2,degeneration:4,convergence:2,equivariance:5,representative:6};
for(const c of chapters)if(c.source==='MHS_EQUIV')c.page=pages[c.id]||1;

// Start with the geometric cochain model; general algebra is linked, not repeated.
const pair=(zh,en)=>[zh,en];
const step=(zh,en,formulas,text)=>({title:pair(zh,en),formulas,text});
const model=by('complex');
const modelProof=model.proof;
model.no='1.1';model.title=pair('复代数簇的奇异上链','Singular cochains of complex varieties');
model.intro=pair(R`取复代数簇族 $X_p$ 及面映射 $d_i^{(p+1)}:X_{p+1}\to X_p$，满足第二节所述的单纯关系。$X_p^{\mathrm{an}}$ 表示其解析空间。`,R`Take complex algebraic varieties $X_p$ and face maps $d_i^{(p+1)}:X_{p+1}\to X_p$ satisfying the simplicial identities of Section 2. Write $X_p^{\mathrm{an}}$ for the associated analytic space.`);
model.formulas=[R`K^{p,q}:=C^q_{\mathrm{sing}}(X_p^{\mathrm{an}},\mathbb Q)`,R`C^q_{\mathrm{sing}}(X_p^{\mathrm{an}},\mathbb Q)=\operatorname{Hom}_{\mathbb Q}(C_q^{\mathrm{sing}}(X_p^{\mathrm{an}},\mathbb Q),\mathbb Q)`,R`K^{p,q}=0\quad(p<0\ \text{or}\ q<0)`];
model.tag=pair('此构造不要求光滑或射影','This construction requires neither smoothness nor projectivity');
model.proof=[step('奇异上链空间','The singular cochain space',[R`d_{\mathrm{sing}}a=a\circ\partial_{\mathrm{sing}}`],pair(R`$C_q^{\mathrm{sing}}$ 是由连续奇异 $q$-单形生成的有理链空间；其对偶为这里的 $K^{p,q}$。奇异上链对任意拓扑空间都有定义；面映射的连续性和单纯关系足以构造该双复形。第二节给出族 $X_\bullet$ 的完整定义。`,R`The rational singular chain space $C_q^{\mathrm{sing}}$ is generated by continuous singular $q$-simplices. Its dual is $K^{p,q}$. Singular cochains are defined for every topological space; continuity of the face maps and the simplicial identities suffice for this double-complex construction. Section 2 gives the full definition of $X_\bullet$.`))];
model.refs=[{course:'mhs',entry:'2.1',label:pair('单纯对象的完整定义','Full definition of the simplicial object')},{course:'spectral',entry:'1.1',label:pair('一般双复形：谱序列 §1','General double complexes: Spectral §1')}];
const differentials={id:'differentials',no:'1.2',kind:'definition',source:'MHS_EQUIV',page:1,graph:'complex',title:pair('面拉回与带符号的微分','Face pullbacks and signed differentials'),formulas:[R`\delta_1^{p,q}:=\sum_{i=0}^{p+1}(-1)^i(d_i^{(p+1)})^*:K^{p,q}\longrightarrow K^{p+1,q}`,R`\delta_2^{p,q}:=(-1)^p d_{\mathrm{sing}}:K^{p,q}\longrightarrow K^{p,q+1}`],proof:modelProof.slice(0,2),refs:[{course:'spectral',entry:'1.5',label:pair('反交换约定','Anticommuting convention')}]};
const total={id:'total-complex',no:'1.3',kind:'definition',source:'MHS_EQUIV',page:1,graph:'filtration',title:pair('本文的总复形与列滤过','Our total complex and column filtration'),intro:pair('对上述具体双复形沿用谱序列课件的构造与记号。','Apply the constructions and notation of the spectral-sequence notes to this specific double complex.'),formulas:[R`C^n:=\bigoplus_{p+q=n}C^q_{\mathrm{sing}}(X_p^{\mathrm{an}},\mathbb Q),\qquad D:=\delta_1+\delta_2`,R`F^pC^n:=\bigoplus_{i\ge p}K^{i,n-i}`,R`F^pH_C^n:=\operatorname{im}\bigl(H^n(F^pC^\bullet,D)\to H^n(C^\bullet,D)\bigr)`],proof:[step('与谱序列课件一致的滤过','The same filtration as in the spectral notes',[R`H_C^n:=H^n(C^\bullet,D)`],pair('这里固定的是列滤过及其自然诱导的上同调滤过。一般构造见下方引用；第二节将它传递到单纯上同调并记为 L。','We fix the column filtration and its induced cohomology filtration. The general construction is linked below. Section 2 transports it to simplicial cohomology and denotes it by L.'))],refs:[{course:'spectral',entry:'1.9',part:2,label:pair('微分保持滤过','The differential preserves the filtration')},{course:'spectral',entry:'1.12',label:pair('诱导上同调滤过','Induced cohomology filtration')}]};
const simplicial=by('simplicial');simplicial.no='2.1';
simplicial.intro=pair(R`设 $X_\bullet:\Delta^{\mathrm{op}}\to\mathrm{Sch}_{\mathbb C}$ 为单纯概形，每个 $X_p$ 是复代数簇（也允许有限不交并）。给定单纯自映射 $f_\bullet$，其各层分量记为 $f_p$。`,R`Let $X_\bullet:\Delta^{\mathrm{op}}\to\mathrm{Sch}_{\mathbb C}$ be a simplicial scheme, each $X_p$ a complex algebraic variety or a finite disjoint union of such varieties. Let $f_\bullet$ be a simplicial endomorphism with components $f_p$.`);
simplicial.formulas.unshift(R`X_\bullet=(X_p,d_i^{(p)},s_i^{(p)})_{p\ge0}`);
simplicial.proof[2].text=pair(R`取拉回后几何交换方块仍交换。这是第三节中 $T\delta_1=\delta_1T$ 的逐项来源。`,R`Pullback preserves the commutative square. This gives $T\delta_1=\delta_1T$ term by term in Section 3.`);

const transported=by('filtrations');transported.no='2.2';transported.title=pair('单纯上同调与滤过 L','Simplicial cohomology and its filtration L');
transported.formulas=[R`H_X^n:=H^n(X_\bullet,\mathbb Q)=H^n(C^\bullet,D)=H_C^n`,R`L^pH_X^n:=F^pH_C^n`,R`\operatorname{Gr}_L^pH_X^n\cong\operatorname{Gr}_F^pH_C^n`];
transported.proof=[step('传递既定滤过','Transport the specified filtration',[R`[a]_D\in L^pH_X^n\ \Longleftrightarrow\ \exists b\in F^pC^n:\ Db=0,\ [b]_D=[a]_D`],pair(R`按 $H_X^n=H_C^n$ 把第一节的诱导滤过 $F$ 记为 $L$。它不是另行选取的滤过；此处也没有引入额外的簇 $X$ 或断言上同调下降。`,R`Under $H_X^n=H_C^n$, write the induced filtration $F$ of Section 1 as $L$. It is not an independently chosen filtration. No additional variety $X$ or descent identification is asserted here.`))];
const hodge=by('hodge');hodge.no='2.3';
hodge.formulas.unshift(R`W_wH_X^n:=L^{n-w}H_X^n,\qquad\operatorname{Gr}_q^WH_X^{p+q}=\operatorname{Gr}_L^pH_X^{p+q}`);
hodge.intro=pair(R`从本节起，为使用纯 Hodge 理论，另假设各 $X_p$ 为有限个光滑射影复簇的不交并。置 $V=H_X^n$。$W$ 是有理空间上的权重滤过，$F_{\mathrm{Hdg}}$ 是复化上的 Hodge 滤过；混合 Hodge 结构简称 MHS。`,R`From this subsection onward, to apply pure Hodge theory, additionally assume that each $X_p$ is a finite disjoint union of smooth projective complex varieties. Put $V=H_X^n$. The weight filtration $W$ is rational, and the Hodge filtration $F_{\mathrm{Hdg}}$ is on the complexification. MHS abbreviates mixed Hodge structure.`);
const formStep=hodge.proof[0];formStep.formulas.push(R`c_n:H^n(\mathcal B^\bullet,D_{\mathcal B})\xrightarrow{\sim}H_X^n\otimes\mathbb C`,R`F_{\mathrm{Hdg}}^\ell H_{X,\mathbb C}^n:=c_n\!\left(\operatorname{im}\bigl(H^n(F_{\mathrm{Hdg}}^\ell\mathcal B^\bullet)\to H^n(\mathcal B^\bullet)\bigr)\right)`);
by('goal').no='3.1';by('action').no='3.2';by('pages').no='3.3';by('convergence').no='3.4';by('degeneration').no='3.5';by('equivariance').no='3.6';by('representative').no='3.7';by('example').no='4.1';by('descent').no='4.2';
by('convergence').proof[2].text=pair('收敛识别稳定页。下一小节利用权重把稳定页识别为第二页。Deligne 的滤过相容性还使收敛比较与 Hodge 滤过相容。','Convergence identifies the stable page. The next subsection uses weights to identify it with the second page. Deligne’s compatibility also makes the convergence comparison respect the Hodge filtration.');
const ordered=[model,differentials,total,simplicial,transported,hodge,by('goal'),by('action'),by('pages'),by('convergence'),by('degeneration'),by('equivariance'),by('representative'),by('example'),by('descent')];
chapters.splice(0,chapters.length,...ordered);
by('goal').proof[1].formulas=[R`X_p=\coprod_{\lambda\in I_p}X_{p,\lambda},\qquad |I_p|<\infty`];
by('goal').proof[2].formulas=[R`(X_\bullet,f_\bullet)\longmapsto(C^\bullet,D,F,T)`,R`E_2^{p,q}\cong E_\infty^{p,q}\cong\operatorname{Gr}_F^pH^{p+q}(C^\bullet,D)`];
by('convergence').proof[1].title=pair('同一个商给出诱导滤过的分次','The same quotient gives the induced graded space');
by('action').proof[0].text=pair(R`第一式逐项来自单纯自映射的面交换关系；第二式来自奇异微分的自然性。乘上纵向符号后仍有 $T\delta_2=\delta_2T$。`,R`The first identity follows termwise from the face relations; the second is naturality of the singular differential. Including the vertical sign still gives $T\delta_2=\delta_2T$.`);
by('action').proof[1].text=pair(R`$T$ 保持每个双次数，故保持 $F$ 以及传递后的 $L,W$。形式模型中的全纯拉回保持类型，因而保持 $F_{\mathrm{Hdg}}$。de Rham 比较的自然性对应这两个作用。`,R`Since $T$ preserves each bidegree, it preserves $F$ and the transported filtrations $L,W$. Holomorphic pullback in the form model preserves type and hence $F_{\mathrm{Hdg}}$. Naturality of de Rham comparison identifies the actions.`);
