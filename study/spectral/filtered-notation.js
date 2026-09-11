const R=String.raw;
// Keep McCleary's total-cochain convention. We explicitly extend the same
// subspace formulas to the auxiliary index -1 so the page quotient includes
// r=0; there is no E_{-1} page.
export const cycleDefinition=R`Z_s^{p,q}:=F^pC^{p+q}\cap D^{-1}(F^{p+s}C^{p+q+1})`;
export const boundaryDefinition=R`B_s^{p,q}:=F^pC^{p+q}\cap D(F^{p-s}C^{p+q-1})`;
export const filteredSubspaces=[cycleDefinition,boundaryDefinition].map(tex=>R`\begin{gathered}${tex.replaceAll('_s','_r').replaceAll('+s','+r').replaceAll('-s','-r')}\\(r\ge-1)\end{gathered}`);
export function pageQuotientTex(index='r'){
 const previous=typeof index==='number'?index-1:`${index}-1`;
 return R`E_{${index}}^{p,q}:=\frac{Z_{${index}}^{p,q}}{Z_{${previous}}^{p+1,q-1}+B_{${previous}}^{p,q}}`;
}
export const generalPageDefinition=R`\begin{gathered}${pageQuotientTex()}\\(r\ge0)\end{gathered}`;
