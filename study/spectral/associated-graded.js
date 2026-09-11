import {replaceMathContent} from './math-transitions.js?v=64';
const R=String.raw;
export const gradedFormulas=[
 R`\operatorname{Gr}_F^pC^n:=\frac{F^pC^n}{F^{p+1}C^n}`,
 R`\begin{gathered}\operatorname{Gr}_F^pD:\\[-.2em]\begin{array}{rcl}\operatorname{Gr}_F^pC^n&\longrightarrow&\operatorname{Gr}_F^pC^{n+1}\\[.25em][a]&\longmapsto&[Da]\end{array}\end{gathered}`
];
// Each left-hand formula has one concise exposition; no independent proof steps.
export function createGradedProof({board,math,language}){
 const t=(zh,en)=>language()==='en'?en:zh;
 const entries={
  graded:{
   f:[
    R`F^pC^n=K^{p,n-p}\oplus F^{p+1}C^n`,
    R`\begin{array}{rcl}K^{p,n-p}&\xrightarrow{\sim}&\operatorname{Gr}_F^pC^n\\[.3em]a&\longmapsto&[a]=a+F^{p+1}C^n\end{array}`
   ],
   note:['由上述直和分解得到此典范同构。','The direct sum decomposition gives this canonical isomorphism.']
  },
  gradedmap:{
   f:[
    R`a\in F^pC^n,\qquad Da\in F^pC^{n+1}`,
    R`\begin{aligned}D(a+F^{p+1}C^n)&=Da+D(F^{p+1}C^n)\\&\subseteq Da+F^{p+1}C^{n+1}.\end{aligned}`
   ],
   note:[R`因为 $D$ 保持滤过，$[a]\mapsto[Da]$ 不依赖代表元的选择，因而良好定义。`,R`Since $D$ preserves the filtration, $[a]\mapsto[Da]$ is independent of the representative, hence well-defined.`]
  }
 };
 return {render(state){
  const entry=entries[state.effect];if(!entry)return;
  const html=`<div class="proof-body"><div class="operation-content">${entry.f.map(f=>`<div class="operation-equation">${math(f,true)}</div>`).join('')}</div><p class="operation-note">${t(...entry.note).replace(/\$([^$]+)\$/g,(_,tex)=>math(tex))}</p></div>`;
  replaceMathContent(board,html);board.dataset.currentProofTopic='graded';board.dataset.currentProofStep=state.effect==='gradedmap'?'1':'0';
 }};
}
