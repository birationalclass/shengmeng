// Shared metre-based architectural model for the drawing and the 3D shell.
export const VILLA_PLAN={outer:[-18,18,-14,14],court:[-6,6,-6,6],wall:.28,floor:.9,privateHeight:3.6,publicHeight:4.8,doorHeight:2.8,corridor:2,
 roofs:[[-12,0,12,28,3.6],[12,0,12,28,4.8],[0,-10,12,8,3.6],[0,10,12,8,3.6]],
 rooms:[
 {id:'library',name:'研究书房',bounds:[-18,-8,-14,-4],zone:'work'},
 {id:'bath',name:'主卫',bounds:[-18,-13,-4,4],zone:'private'},
 {id:'dressing',name:'衣帽间',bounds:[-13,-8,-4,4],zone:'private'},
 {id:'bedroom',name:'主卧',bounds:[-18,-8,4,14],zone:'private'},
 {id:'west-gallery',name:'私密走廊',bounds:[-8,-6,-14,14],zone:'circulation'},
 {id:'gallery',name:'数学展廊',bounds:[-6,6,-14,-6],zone:'work'},
 {id:'studio',name:'AI 工作室',bounds:[6,18,-14,-6],zone:'work'},
 {id:'dining',name:'餐厅',bounds:[8,14,-6,3],zone:'public'},
 {id:'kitchen',name:'厨房',bounds:[14,18,-6,3],zone:'service'},
 {id:'east-gallery',name:'通廊',bounds:[6,8,-6,3],zone:'circulation'},
 {id:'living',name:'海景会客厅',bounds:[6,18,3,14],zone:'public'},
 {id:'entry',name:'玄关 / 画廊',bounds:[-2,6,6,14],zone:'public'},
 {id:'cloak',name:'衣帽储藏',bounds:[-6,-2,6,10],zone:'service'},
 {id:'wc',name:'客卫',bounds:[-6,-2,10,14],zone:'service'}]};
export const roomArea=room=>(room.bounds[1]-room.bounds[0])*(room.bounds[3]-room.bounds[2]);
export const villaFootprint=36*28-12*12;
