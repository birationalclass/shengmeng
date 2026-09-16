const R=String.raw;
export const singleLineTitle=['推论：单列或单行的收敛','Corollary: Single-column or single-row convergence'];
export const singleLineFormula=R`\begin{gathered}E_{r_0}^{p,q}\Longrightarrow H^{p+q}\\E_{r_0}^{p,q}=0\ (p>0)\\\Longrightarrow\ H^n\cong E_{r_0}^{0,n}\\E_{r_0}^{p,q}=0\ (q>0)\\\Longrightarrow\ E_{r_0}^{n,0}\cong H^n\end{gathered}`;

// This statement concerns an abstract convergent spectral sequence, not a
// particular sheaf or double complex. Fix the finite target filtration explicitly.
export function singleLineContent({math,t}){
 const eq=x=>`<div class="operation-equation">${math(x,true)}</div>`,para=x=>`<p>${x}</p>`;
 const setup=t(`设第一象限上同调型谱序列收敛到带有限滤过的 ${math(R`H^\bullet`)}，${math(R`r_0\ge2`)}。以下两个条件分别使用。`,`Let a first-quadrant cohomological spectral sequence converge to ${math(R`H^\bullet`)} with a finite filtration, ${math(R`r_0\ge2`)}. The following are two separate cases.`);
 const assumptions=t(`设 ${math(R`(E_s^{p,q},d_s)_{s\ge r_0}`)} 是第一象限上同调型谱序列，${math(R`r_0\ge2`)}，微分双次数为 ${math('(s,1-s)')}。设它收敛到 ${math(R`H^\bullet`)}，具体指对每个 ${math(R`n\ge0`)}，给定有限滤过及相容同构：`,`Let ${math(R`(E_s^{p,q},d_s)_{s\ge r_0}`)} be a first-quadrant cohomological spectral sequence with ${math(R`r_0\ge2`)} and differentials of bidegree ${math('(s,1-s)')}. Assume it converges to ${math(R`H^\bullet`)}: for each ${math(R`n\ge0`)}, fix a finite filtration and compatible isomorphisms:`);
 const filtration=[R`H^n=F^0H^n\supseteq\cdots\supseteq F^{n+1}H^n=0`,R`E_\infty^{p,n-p}\cong F^pH^n/F^{p+1}H^n`];
 const conclusions=[R`\bigl[E_{r_0}^{p,q}=0\ (p>0,\ q\ge0)\bigr]\ \Longrightarrow\ H^n\xrightarrow{\sim}E_{r_0}^{0,n}`,R`\bigl[E_{r_0}^{p,q}=0\ (q>0,\ p\ge0)\bigr]\ \Longrightarrow\ E_{r_0}^{n,0}\xrightarrow{\sim}H^n`];
 const detail=para(t('先设只剩第零列。零项在后续页仍为零；对每个后续页，唯一可能非零的项的入射与出射微分如下：','Suppose only column zero remains. Zero terms remain zero on later pages. On each later page, the incoming and outgoing differentials at a possibly nonzero term are'))+
 eq(R`\underbrace{E_s^{-s,n+s-1}}_{0}\xrightarrow{d_s^{-s,n+s-1}}E_s^{0,n}\xrightarrow{d_s^{0,n}}\underbrace{E_s^{s,n-s+1}}_{0}\qquad(s\ge r_0)`)+
 para(t(`第一项因第一象限条件为零，第三项因其列指标为正而为零。这里仅需 ${math(R`s\ge r_0\ge1`)}，故单列结论实际在 ${math(R`r_0\ge1`)} 时就成立。其它位置的项为零，其出射微分也为零。因此所有后续微分均为零，引用 2.14：`,`The source is zero by the first-quadrant condition, and the target is zero because its column is positive. This only requires ${math(R`s\ge r_0\ge1`)}, so the single-column assertion already holds for ${math(R`r_0\ge1`)}. All other terms are zero, so their outgoing differentials also vanish. Thus every later differential is zero, and 2.14 applies:`))+
 eq(R`d_s=0\quad(s\ge r_0)\quad\overset{2.14}{\Longrightarrow}\quad E_{r_0}^{p,q}\cong E_\infty^{p,q}`)+
 eq(R`E_{r_0}^{p,n-p}=0\ \Longrightarrow\ E_s^{p,n-p}=0\ (s\ge r_0)\ \Longrightarrow\ E_\infty^{p,n-p}=0\qquad(1\le p\le n)`)+
 para(t('由收敛给出的同构，对每个正的滤过指标，','By the convergence isomorphisms, for each positive filtration index,'))+
 eq(R`\frac{F^pH^n}{F^{p+1}H^n}\cong E_\infty^{p,n-p}=0\quad\Longrightarrow\quad F^pH^n=F^{p+1}H^n\qquad(1\le p\le n)`)+
 para(t('将这些等式与假设中的零端点相接，得到','Combining these equalities with the assumed zero endpoint gives'))+
 eq(R`F^1H^n=F^2H^n=\cdots=F^{n+1}H^n=0`)+
 eq(R`\therefore\quad F^pH^n=0\qquad(1\le p\le n+1)`)+
 para(t('因此第零个滤过商就是整个目标，且第零列已经稳定：','Thus the zeroth filtration quotient is the entire target, and column zero has stabilized:'))+
 eq(R`H^n=F^0H^n\xrightarrow{\sim}\frac{F^0H^n}{F^1H^n}\xrightarrow{\sim}E_\infty^{0,n}\xrightarrow{\sim}E_{r_0}^{0,n}`)+
 para(t(`其中第一个箭头是商映射，因为 ${math(R`F^1H^n=0`)} 而为同构。零端点 ${math(R`F^{n+1}H^n=0`)} 是假设；仅有各商为零只能推出相邻滤过项相等。`,`The first arrow is the quotient map, an isomorphism because ${math(R`F^1H^n=0`)}. The zero endpoint ${math(R`F^{n+1}H^n=0`)} is an assumption; vanishing quotients alone only imply equality of adjacent filtration terms.`))+
 para(t('再设只剩第零行。此时后续微分为','Now suppose only row zero remains. The later differentials are'))+
 eq(R`\underbrace{E_s^{n-s,s-1}}_{0}\xrightarrow{d_s^{n-s,s-1}}E_s^{n,0}\xrightarrow{d_s^{n,0}}\underbrace{E_s^{n+s,1-s}}_{0}\qquad(s\ge r_0\ge2)`)+
 para(t(`<strong>这里用到 ${math(R`r_0\ge2`)}：</strong>对每个 ${math(R`s\ge r_0`)}，有 ${math(R`s-1>0`)} 和 ${math(R`1-s<0`)}。因此入射源因位于正行而为零，出射目标因位于负行而为零。其它位置的项为零，故全部后续微分均为零。再引用 2.14，并使用收敛的滤过：`,`<strong>This is where ${math(R`r_0\ge2`)} is used:</strong> for every ${math(R`s\ge r_0`)}, we have ${math(R`s-1>0`)} and ${math(R`1-s<0`)}. Thus the incoming source vanishes because its row is positive, and the outgoing target vanishes because its row is negative. All other terms are zero, so all later differentials vanish. Apply 2.14 and then the convergence filtration:`))+
 eq(R`d_s=0\quad(s\ge r_0)\quad\overset{2.14}{\Longrightarrow}\quad E_{r_0}^{p,q}\cong E_\infty^{p,q}`)+
 eq(R`E_{r_0}^{p,n-p}=0\ \Longrightarrow\ E_s^{p,n-p}=0\ (s\ge r_0)\ \Longrightarrow\ E_\infty^{p,n-p}=0\qquad(0\le p<n)`)+
 eq(R`\frac{F^pH^n}{F^{p+1}H^n}\cong E_\infty^{p,n-p}=0\quad\Longrightarrow\quad F^pH^n=F^{p+1}H^n\qquad(0\le p<n)`)+
 para(t('这次从滤过的首端开始，得到','This time, starting from the first filtration term gives'))+
 eq(R`H^n=F^0H^n=F^1H^n=\cdots=F^nH^n,\qquad F^{n+1}H^n=0`)+
 eq(R`E_{r_0}^{n,0}\xrightarrow{\sim}E_\infty^{n,0}\xrightarrow{\sim}\frac{F^nH^n}{F^{n+1}H^n}\xrightarrow{\sim}H^n`)+
 para(t(`若 ${math('r_0=1')}，则 ${math('s=1')} 时两端的行指标都是零，不能据此断言微分为零：`,`If ${math('r_0=1')}, then at ${math('s=1')} both adjacent row indices are zero, so the vanishing argument fails:`))+
 eq(R`E_1^{n-1,0}\xrightarrow{d_1^{n-1,0}}E_1^{n,0}\xrightarrow{d_1^{n,0}}E_1^{n+1,0}`)+
 para(t(`因此单行条件下，${math('r_0=1')} 还需额外假设 ${math('d_1=0')}，才能得到同样结论。`,`Thus, in the single-row case, ${math('r_0=1')} requires the additional assumption ${math('d_1=0')} to obtain the same conclusion.`))+
 para(t('这些同构是相对于给定收敛数据的边缘同构。关键在于总次数 n 仅有一个可能非零的滤过商；一般的退化并不能把每个稳定项与整个 Hⁿ 等同。','These are the edge isomorphisms relative to the given convergence data. The key is that total degree n has only one possibly nonzero filtration quotient; degeneration alone does not identify each stable term with the whole of Hⁿ.'));
 return {setup,assumptions,filtration,conclusions,f:[R`H^n\cong E_\infty^{0,n}\cong E_{r_0}^{0,n}\quad\text{(only column 0)}`,R`E_{r_0}^{n,0}\cong E_\infty^{n,0}\cong H^n\quad\text{(only row 0)}`].map(x=>t(x.replace('only column 0','仅第零列').replace('only row 0','仅第零行'),x)),note:t('微分的源或目标为零，使各页稳定；收敛再将唯一可能非零的滤过商识别为整个目标。因此目标消失时，这个剩余项也为零。','Vanishing sources or targets force stabilization. Convergence then identifies the sole possibly nonzero filtration quotient with the whole target. If the target vanishes, the surviving term also vanishes.'),detail};
}

export function singleLineDiagram({label,t}){
 let svg='',labels=label(420,38,R`E_{r_0}^{p,q}\Longrightarrow H^{p+q}\qquad(r_0\ge2)`,800,'title');
 for(const [side,origin] of [['column',90],['row',505]]){
  const column=side==='column';
  labels+=label(origin+120,105,column?R`p>0:\ E_{r_0}^{p,q}=0`:R`q>0:\ E_{r_0}^{p,q}=0`,365,'small');
  for(let p=0;p<3;p++)for(let q=0;q<3;q++){
   const x=origin+p*115,y=345-q*82,alive=column?p===0:q===0;
   svg+=`<circle cx="${x}" cy="${y}" r="${alive?23:18}" fill="${alive?'#77d8cc0c':'none'}" stroke="${alive?'#77d8cc66':'#47636822'}"/>`;
   labels+=label(x,y,alive?`E_{r_0}^{${p},${q}}`:'0',105,alive?'gold':'small');
  }
  labels+=label(origin+120,420,column?R`H^n\cong E_{r_0}^{0,n}`:R`E_{r_0}^{n,0}\cong H^n`,370,'gold');
 }
 return `<svg viewBox="0 0 840 525" role="img" aria-label="${t('仅第零列或第零行可能非零时，剩余项与目标同构','Only column zero or row zero survives, identifying the remaining term with the target')}">${svg}</svg>${labels}`;
}
