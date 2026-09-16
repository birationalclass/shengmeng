const R=String.raw;

// The source's notation is local to this proof: f:Y -> X, L(mH), i,j; only the twisting parameter is renamed m.
// Do not apply the notebook's sheaf-letter or twist-parameter substitutions here.
export function kmVanishingProof({math,t}){
 const eq=x=>`<div class="operation-equation">${math(x,true)}</div>`,p=x=>`<p>${x}</p>`;
 const assumptions=t(`沿用 Kollár–Mori (2.64) 证明 Step 4 的记号。设 ${math('X')} 为光滑复射影簇，${math('L')} 为 ${math('X')} 上 nef 且 big 的线丛，${math('H')} 为充足除子。取光滑射影簇 ${math('Y')} 及双有理态射 ${math(R`f:Y\to X`)}，满足下式，其中 ${math('A')} 为充足有理除子，${math('E')} 的支集为简单正规交叉除子：`,`Use the notation of Kollár–Mori (2.64), Step 4. Let ${math('X')} be smooth complex projective, ${math('L')} a nef and big line bundle on ${math('X')}, and ${math('H')} an ample divisor. Choose ${math('Y')} smooth projective and ${math(R`f:Y\to X`)} birational, with ${math('A')} ample and ${math('E')} supported on a simple normal crossing divisor:`);
 const hypothesisFormulas=[R`f^*L\equiv A+E,\qquad E=\sum_j e_jE_j,\qquad 0\le e_j<1`];
 const conclusionLead=t('则高阶直像与所需的上同调群消失：','Then the higher direct images and the required cohomology vanish:');
 const conclusions=[R`R^jf_*\omega_Y=0\quad(j>0)`,R`H^i(X,\omega_X\otimes L)=0\quad(i>0)`];
 const detail=p(t(`记 ${math(R`L(mH)=L\otimes\mathcal O_X(mH)`)}；将原文的扭曲次数 ${math('r')} 改记为 ${math('m')}，其余记号沿用原文。由 Step 3 已证的充足情形，对每个整数 ${math(R`m\ge0`)} 有`,`Here ${math(R`L(mH)=L\otimes\mathcal O_X(mH)`)}; write ${math('m')} for the source’s twisting parameter ${math('r')}. The ample case proved in Step 3 gives, for every integer ${math(R`m\ge0`)},`))+
 eq(R`f^*L(mH)\equiv(A+mf^*H)+E,\qquad A+mf^*H\text{ ample}`)+
 eq(R`H^k(Y,f^*L(mH)\otimes\omega_Y)=0\qquad(k>0)`)+
 p(t('投影公式与 Leray 谱序列给出','Projection formula and Leray give'))+
 eq(R`H^i(X,L(mH)\otimes R^jf_*\omega_Y)\Longrightarrow H^{i+j}(Y,\omega_Y\otimes f^*L(mH))`)+
 p(t(`先取 ${math(R`m\gg1`)}。Serre 消失给出`,`For ${math(R`m\gg1`)}, Serre vanishing gives`))+
 eq(R`H^i(X,L(mH)\otimes R^jf_*\omega_Y)=0\qquad(i>0)`)+
 p(t(`只剩 ${math('i=0')} 一列。由 3.14，`,`Only column ${math('i=0')} remains. By 3.14,`))+
 eq(R`H^0(X,L(mH)\otimes R^jf_*\omega_Y)\cong H^j(Y,\omega_Y\otimes f^*L(mH))=0\qquad(j>0)`)+
 p(t(`充分大的扭曲 ${math(R`L(mH)\otimes R^jf_*\omega_Y`)} 由全局截面生成，故该层为零，从而 ${math(R`R^jf_*\omega_Y=0`)}（${math('j>0')}）。最后取 ${math('m=0')}，由 3.14 的单行情形得到`,`The sufficiently large twist ${math(R`L(mH)\otimes R^jf_*\omega_Y`)} is globally generated, hence zero. Thus ${math(R`R^jf_*\omega_Y=0`)} for ${math('j>0')}. Now set ${math('m=0')}; the single-row case of 3.14 yields`))+
 eq(R`H^i(X,L\otimes f_*\omega_Y)\cong H^i(Y,f^*L\otimes\omega_Y)=0\qquad(i>0)`)+
 p(t(`光滑簇之间的适当双有理态射满足 ${math(R`f_*\omega_Y\cong\omega_X`)}，故这正是所需结论。`,`Since ${math(R`f_*\omega_Y\cong\omega_X`)} for a proper birational morphism between smooth varieties, this is the required conclusion.`));
 return {assumptions,hypothesisFormulas,conclusionLead,conclusions,detail};
}
