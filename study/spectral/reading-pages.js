import {singleLineTitle} from './single-line-convergence.js?v=153';
import {firstQuadrantTitle} from './first-quadrant-convergence.js?v=155';
import {hodgeTitles} from './hodge.js?v=155';
import {lerayTitles} from './leray.js?v=155';
// A numbered entry is a persistent semantic unit, not a replaceable slide slot.
// A map and its representative rule, or the two sides of an equality, stay together.
const groups={
 'learn:3':{section:2,first:6,items:[[1,2]]},
 'learn:6':{section:1,first:14,items:[[1],[2],[3]]},
 'learn:4':{section:2,first:7,items:[[1,2,3]]},
 'learn:5':{section:2,first:1,items:[[3],[4]],actions:[[1,2,3],[4]],focus:[3,4]},
 'converge:0':{section:2,first:3,items:[[1],[2],[3,4,5,6]]},
 'converge:1':{section:2,first:10,items:[[1]]},
 'converge:2':{section:2,first:11,items:[[1,2]]},
 'converge:3':{section:2,first:8,items:[[1],[2],[4],[5]]},
 'converge:5':{section:3,first:1,items:Array.from({length:hodgeTitles.length},(_,i)=>[i+1])},
 'converge:4':{section:4,first:1,items:Array.from({length:lerayTitles.length},(_,i)=>[i+1])}
};
const kinds={
 'learn:3':['E'],'learn:6':['D','D','P'],'learn:4':['D'],'learn:5':['D','D'],
 'converge:0':['P','D','P'],'converge:1':['D'],'converge:2':['D'],'converge:3':['D','T','D','C'],
 'converge:5':['D','D','P','D','T','T'],
 'converge:4':['','D','D','D','D','L','D','D','D','D','P','P','T','E','E']
};
export function numberedPages(module,step,count){
 const group=groups[`${module}:${step}`]||{section:2,first:module==='lab'?20:22,items:Array.from({length:count},(_,i)=>[i+1])};
 return group.items.map((indices,i)=>({indices,kind:kinds[`${module}:${step}`]?.[i],actions:group.actions?.[i]??indices,focus:group.focus?.[i]??indices[0],number:`${group.section}.${group.first+i}`,title:titles[`${module}:${step}`]?.[i]}));
}

// Short headings remain readable while their formula bodies are folded.
const titles={
 'learn:3':[{name:['第零页','Zeroth page'],symbol:'(E_0,d_0)'}],
 'learn:6':[{name:['滤过闭元','Filtered cocycles'],symbol:'Z_r'},{name:['滤过边界','Filtered boundaries'],symbol:'B_r'},['命题：包含关系','Proposition: Inclusions']],
 'learn:4':[['谱序列','Spectral sequence']],
 'learn:5':[{name:['一般页','General page'],symbol:'E_r'},{name:['微分','Differential'],symbol:'d_r'}],
 'converge:0':[['性质：逐页上同调','Property: Page cohomology'],['自然过渡映射','Natural transition map'],['命题：逐位置稳定','Proposition: Pointwise stabilization']],
 'converge:1':[{name:['稳定页','Stable page'],symbol:String.raw`E_\infty`}],
 'converge:2':[['上同调的诱导滤过','Induced filtration on cohomology']],
 'converge:3':[{name:['收敛','Convergence'],symbol:String.raw`\Longrightarrow`},firstQuadrantTitle,['退化','Degeneration'],singleLineTitle],
 'converge:4':lerayTitles,
 'converge:5':hodgeTitles,
 'lab:0':[{name:['页','Page'],symbol:'E_r'},{name:['微分','Differential'],symbol:'d_r'}]
};
