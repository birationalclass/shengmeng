export function elementOrder(group,element){
 let power=group.e;
 for(let order=1;order<=group.table.length;order++){
  power=group.table[power][element];if(power===group.e)return order;
 }
 throw new Error('Element has no finite order');
}
// A visual hierarchy, not an astrophysical mass classification.
export function celestialRank(order){
 if(order===1)return {type:'black-hole',zh:'黑洞',en:'Black hole',scale:1.7};
 if(order===2)return {type:'blue-star',zh:'蓝白巨星',en:'Blue-white giant',scale:1.3};
 if(order===3)return {type:'gold-star',zh:'金色恒星',en:'Golden star',scale:1.06};
 if(order===4)return {type:'red-star',zh:'红色恒星',en:'Red star',scale:.88};
 if(order===5)return {type:'gas-planet',zh:'气态行星',en:'Gas planet',scale:.73};
 return {type:'ice-planet',zh:'冰岩行星',en:'Icy planet',scale:Math.max(.38,.65*Math.sqrt(6/order))};
}
