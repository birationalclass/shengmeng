export function elementOrder(group,element){
 let power=group.e;
 for(let order=1;order<=group.table.length;order++){
  power=group.table[power][element];if(power===group.e)return order;
 }
 throw new Error('Element has no finite order');
}
// Relative rank within this group's distinct element orders; decorative subtypes share a size.
export function celestialRank(order,distinctOrders=[1,2,3],seed=0){
 if(order===1)return {type:'black-hole',zh:'黑洞',en:'Black hole',scale:1};
 const stellarOrder=[...new Set(distinctOrders)].filter(n=>n>1).sort((a,b)=>a-b)[0];
 if(order===stellarOrder){const types=['gold-star','blue-star','red-star'],zh=['金色恒星','蓝白恒星','红色恒星'];return {type:types[seed%3],zh:zh[seed%3],en:'Star',scale:.8};}
 const types=['ocean-planet','gas-planet','ice-planet','ring-planet'];return {type:types[seed%4],zh:['海洋行星','气态行星','冰岩行星','环状行星'][seed%4],en:'Planet',scale:.6};
}
export function conjugacyClasses(group){
 const n=group.table.length,inverses=group.table.map(row=>row.indexOf(group.e)),seen=new Set(),classes=[];
 for(let x=0;x<n;x++){
  if(seen.has(x))continue;
  const members=[...new Set(inverses.map((inverse,g)=>group.table[group.table[g][x]][inverse]))].sort((a,b)=>a-b);
  members.forEach(member=>seen.add(member));classes.push(members);
 }
 return classes;
}
export function celestialLayout(group,seed=71){
 const orders=group.labels.map((_,i)=>elementOrder(group,i)),distinct=[...new Set(orders)].sort((a,b)=>a-b);
 const classes=conjugacyClasses(group),classOf=new Map();classes.forEach((members,index)=>members.forEach(i=>classOf.set(i,index)));
 const entries=orders.map((order,i)=>{const classIndex=classOf.get(i),members=classes[classIndex];return {element:i,order,classIndex,classSize:members.length,appearanceSeed:members[0],rank:celestialRank(order,distinct,classIndex),host:null,slot:0};});
 const stars=entries.filter(x=>x.rank.type.endsWith('star'));
 if(new Set(stars.map(x=>x.rank.type)).size===1)for(const star of stars)star.rank={...star.rank,type:'blue-star',zh:'蓝巨星',en:'Blue giant'};
 const shuffled=[...stars];const random=()=>{seed=(seed*16807)%2147483647;return(seed-1)/2147483646;};
 for(let i=shuffled.length-1;i>0;i--){const j=Math.floor(random()*(i+1));[shuffled[i],shuffled[j]]=[shuffled[j],shuffled[i]];}
 let count=0;for(const entry of entries){if(!entry.rank.type.endsWith('planet'))continue;const host=shuffled[count%shuffled.length];entry.host=host.element;entry.slot=Math.floor(count/shuffled.length);entry.phase=random()*Math.PI*2;count++;}
 return entries;
}

export function bodyScale(groupOrder){return .544*Math.min(1.15,Math.pow(6/Math.max(1,groupOrder),.32));}
