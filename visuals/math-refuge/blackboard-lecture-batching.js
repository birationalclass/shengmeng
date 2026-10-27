import {batchStaticHall} from './blackboard-static.js';
const panelName=/^Sliding chalkboard \d+[AB]$/;
const toolName=/^(Writing chalk|Moving blackboard eraser|Temporary spoken laser reference)$/;
// Merge geometry in each panel's own coordinates. Its frame and writing face
// must stay children of the moving panel, never baked into the auditorium.
export function batchLectureGeometry(T,root){
 const panels=[],moving=[];
 root.traverse(object=>{if(panelName.test(object.name)){panels.push(object);moving.push(object);}else if(toolName.test(object.name))moving.push(object);});
 const local=panels.map(panel=>batchStaticHall(T,panel,{freeze:false,opaqueOnly:true}));
 const hall=batchStaticHall(T,root,{exclude:moving,freeze:false,opaqueOnly:true,bucket:(_mesh,matrix)=>Math.max(0,Math.min(2,Math.round((matrix.elements[12]-22.4)/5.6)))});
 return {before:hall.before+local.reduce((sum,x)=>sum+x.before,0),after:hall.after+local.reduce((sum,x)=>sum+x.after,0),batches:hall.batches+local.reduce((sum,x)=>sum+x.batches,0),movingPanels:panels.length,panelLocalBatches:local.reduce((sum,x)=>sum+x.batches,0)};
}
