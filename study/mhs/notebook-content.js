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
