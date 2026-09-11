const R=String.raw;
// McCleary's total-cochain convention. Auxiliary Z and B are defined for
// every integer index; the spectral sequence itself starts at page zero.
export const cycleDefinition=R`Z_s^{p,q}:=F^pC^{p+q}\cap D^{-1}(F^{p+s}C^{p+q+1})`;
export const boundaryDefinition=R`B_s^{p,q}:=F^pC^{p+q}\cap D(F^{p-s}C^{p+q-1})`;
export const filteredSubspaces=[cycleDefinition,boundaryDefinition].map(tex=>tex.replaceAll('_s','_r').replaceAll('+s','+r').replaceAll('-s','-r'));
export function pageQuotientTex(index='r'){
 const previous=typeof index==='number'?index-1:`${index}-1`;
 return R`E_{${index}}^{p,q}:=\frac{Z_{${index}}^{p,q}}{Z_{${previous}}^{p+1,q-1}+B_{${previous}}^{p,q}}`;
}
export const generalPageDefinition=pageQuotientTex();
