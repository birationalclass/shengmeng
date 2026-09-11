// A numbered entry is a persistent semantic unit, not a replaceable slide slot.
// A map and its representative rule, or the two sides of an equality, stay together.
const groups={
 'learn:3':{section:2,first:1,items:[[1],[2]]},
 'learn:4':{section:2,first:3,items:[[1],[2,3]]},
 'learn:5':{section:2,first:5,items:[[3],[4]],actions:[[1,2,3],[4]],focus:[3,4]},
 'converge:0':{section:2,first:7,items:[[1,2,3]]},
 'converge:1':{section:2,first:8,items:[[1]]},
 'converge:2':{section:2,first:9,items:[[1,2]]},
 'converge:3':{section:2,first:10,items:[[1]]}
};
export function numberedPages(module,step,count){
 const group=groups[`${module}:${step}`]||{section:2,first:module==='lab'?20:22,items:Array.from({length:count},(_,i)=>[i+1])};
 return group.items.map((indices,i)=>({indices,actions:group.actions?.[i]??indices,focus:group.focus?.[i]??indices[0],number:`${group.section}.${group.first+i}`,title:titles[`${module}:${step}`]?.[i]}));
}

// Short headings remain readable while their formula bodies are folded.
const titles={
 'learn:3':[{name:['第零页','Zeroth page'],symbol:'E_0'},{name:['微分','Differential'],symbol:'d_0'}],
 'learn:4':[{name:['第一页','First page'],symbol:'E_1'},{name:['微分','Differential'],symbol:'d_1'}],
 'learn:5':[{name:['一般页','General page'],symbol:'E_r'},{name:['微分','Differential'],symbol:'d_r'}],
 'converge:0':[['命题：逐位置稳定','Proposition: Pointwise stabilization']],
 'converge:1':[{name:['稳定页','Stable page'],symbol:String.raw`E_\infty`}],
 'converge:2':[['上同调的诱导滤过','Induced filtration on cohomology']],
 'converge:3':[['收敛到总上同调','Convergence to total cohomology']],
 'lab:0':[{name:['页','Page'],symbol:'E_r'},{name:['微分','Differential'],symbol:'d_r'}]
};
