import {replaceMathContent} from './math-transitions.js?v=64';
const R=String.raw;
export const gradedFormulas=[
 R`\operatorname{Gr}_F^pC^n:=\frac{F^pC^n}{F^{p+1}C^n}`,
 R`\begin{gathered}\operatorname{Gr}_F^pD^n:\\[-.2em]\begin{array}{rcl}\operatorname{Gr}_F^pC^n&\longrightarrow&\operatorname{Gr}_F^pC^{n+1}\\[.25em]a+F^{p+1}C^n&\longmapsto&Da+F^{p+1}C^{n+1}\end{array}\end{gathered}`
];
export function createGradedProof({board,math,language}){
 let step=0,context=null;const t=(zh,en)=>language()==='en'?en:zh;
 const entries=[
  {name:['空间与元素','Spaces and elements'],f:[R`\pi_p^n:F^pC^n\longrightarrow\operatorname{Gr}_F^pC^n`,R`\pi_p^n(a):=a+F^{p+1}C^n,\quad a\in F^pC^n`,R`\ker\pi_p^n=F^{p+1}C^n`],note:['关联分次取出相邻滤过层之间的商。两个代表元给出同一类，当且仅当其差属于下一层滤过。','The associated graded takes quotients of consecutive filtration layers. Two representatives define the same class exactly when their difference lies in the next layer.']},
  {name:['诱导微分','Induced differential'],f:[R`D^n:=D|_{C^n}:C^n\longrightarrow C^{n+1}`,R`D(F^{p+1}C^n)\subseteq F^{p+1}C^{n+1}`,R`\begin{aligned}a'-a\in F^{p+1}C^n\quad&\Longrightarrow\\Da'-Da\in F^{p+1}C^{n+1}.&\end{aligned}`,R`\operatorname{Gr}_F^pD^n\circ\pi_p^n=\pi_p^{n+1}\circ D|_{F^pC^n}`],note:['D 保持滤过，所以它的像仍在目标滤过层；它也保持下一层，因此商上的像不依赖代表元。Gr 不只是空间的记号，也作用于保持滤过的映射。','D preserves the filtration, so its image belongs to the target layer. It also preserves the next layer, making the quotient map independent of representatives. Gr acts on filtration-preserving maps as well as spaces.']},
  {name:['关联分次复形','Associated graded complex'],f:[R`(\operatorname{Gr}_F^pD^{n+1})(\operatorname{Gr}_F^pD^n)=0`,R`\operatorname{Gr}_FC^n:=\bigoplus_p\operatorname{Gr}_F^pC^n`,R`\operatorname{Gr}_FD^n:=\bigoplus_p\operatorname{Gr}_F^pD^n`],note:[R`复合映射把 $a$ 的类送到 $D^2a$ 的类，即零。各 $p$ 对应的上链复形的直和称为关联分次复形；微分保持 $p$，将总次数提高一。`,R`The composite sends the class of $a$ to the class of $D^2a$, which is zero. The direct sum of these cochain complexes is the associated graded complex; its differential preserves $p$ and raises total degree by one.`]},
  {name:['与双复形的关系','Relation to the double complex'],f:[R`\operatorname{Gr}_F^pC^n\cong K^{p,n-p}`,R`\begin{array}{rcl}\Phi^{p,n}:K^{p,n-p}&\xrightarrow{\sim}&\operatorname{Gr}_F^pC^n\\a&\longmapsto&a+F^{p+1}C^n\end{array}`,R`(\operatorname{Gr}_F^pD^n)\Phi^{p,n}=\Phi^{p,n+1}\delta_2^{p,n-p}`,R`\delta_1a\in F^{p+1}C^{n+1}`],note:[R`取商后，横向分量的类为零，纵向分量保留。这是同构下的对应，并非总复形上 $D=\delta_2$。第二节令 $n=p+q$，分别将这两个构造记作 $E_0^{p,q}$ 和 $d_0^{p,q}$。`,R`The horizontal component vanishes in the quotient; the vertical component remains. This identification does not assert $D=\delta_2$ on the total complex. Section 2 sets $n=p+q$ and names the two constructions $E_0^{p,q}$ and $d_0^{p,q}$.`]}
 ];
 function paint(){if(!context)return;const entry=entries[step];let html=`<nav class="proof-steps" aria-label="${t('关联分次的数学阐述','Associated graded exposition')}">${entries.map((e,i)=>`<button type="button" data-graded-proof="${i}" aria-pressed="${i===step}">${i+1}. ${t(...e.name)}</button>`).join('')}</nav><div class="proof-body"><div class="operation-content">${entry.f.map(f=>`<div class="operation-equation">${math(f,true)}</div>`).join('')}</div><p class="operation-note">${t(...entry.note).replace(/\$([^$]+)\$/g,(_,tex)=>math(tex))}</p></div>`;
 if(context.p>context.n)html+=`<p class="operation-note">${math(R`\operatorname{Gr}_F^{${context.p}}C^{${context.n}}=0`)}.</p>`;
 if(context.n===4&&context.p===0&&context.effect==='gradedmap')html+=`<p class="operation-note">${t('目标','The target')} ${math(R`K^{0,5}`)} ${t('位于当前显示窗口之外，不能因此认定它为零。','lies outside the displayed window; it is not assumed zero.')}</p>`;
 html+='<p class="operation-note proof-reference"><a href="https://stacks.math.columbia.edu/tag/012K" target="_blank" rel="noopener">Stacks Project, §12.24</a></p>';
 replaceMathContent(board,html);board.dataset.currentProofTopic='graded';board.dataset.currentProofStep=String(step);
 }
 board.addEventListener('click',event=>{const button=event.target.closest('[data-graded-proof]');if(!button||!context)return;event.stopPropagation();step=Number(button.dataset.gradedProof);paint();});
 return {render(state){context=state;paint();},reset(){context=null;step=0;}};
}
