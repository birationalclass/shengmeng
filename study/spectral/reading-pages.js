// A numbered entry is a persistent semantic unit, not a replaceable slide slot.
// A map and its representative rule, or the two sides of an equality, stay together.
const groups={
 'learn:3':{section:2,first:1,items:[[1],[2]]},
 'learn:4':{section:2,first:3,items:[[1],[2,3]]},
 'learn:5':{section:2,first:5,items:[[1,2,3],[4]],focus:[3,4]},
 'converge:0':{section:2,first:7,items:[[1],[2],[3]]},
 'converge:1':{section:2,first:10,items:[[1],[2],[3]]},
 'converge:2':{section:2,first:13,items:[[1],[2,3]]},
 'converge:3':{section:2,first:15,items:[[1,2],[3,4],[5]]},
 'converge:4':{section:2,first:18,items:[[1],[2]]}
};
export function numberedPages(module,step,count){
 const group=groups[`${module}:${step}`]||{section:2,first:module==='lab'?20:22,items:Array.from({length:count},(_,i)=>[i+1])};
 return group.items.map((indices,i)=>({indices,focus:group.focus?.[i]??indices[0],number:`${group.section}.${group.first+i}`,title:titles[`${module}:${step}`]?.[i]}));
}

// Short headings remain readable while their formula bodies are folded.
const titles={
 'learn:3':['E_0','d_0'],
 'learn:4':['E_1','d_1'],
 'learn:5':['E_r','d_r'],
 'converge:0':['H^n','F^pH^n',String.raw`\operatorname{Gr}_F^pH^n`],
 'converge:1':['F^{p+r}C^{n+1}',String.raw`Z_\infty`,String.raw`B_\infty`],
 'converge:2':[String.raw`E_\infty`,String.raw`\theta^{p,q}`],
 'converge:3':[['同一上同调类','The same cohomology class'],['核的计算','Kernel calculation'],['自然同构','Natural isomorphism']],
 'converge:4':[['收敛','Convergence'],['短正合列','Short exact sequence']],
 'lab:0':['E_r','d_r']
};
