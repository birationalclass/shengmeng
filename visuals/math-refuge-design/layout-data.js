export const STORAGE_KEY='math-refuge-layout-preview-east30-v1';
export function snapshot(layout){return layout.map(b=>({id:b[0],name:b[1],east:b[4],north:b[5],platformWidth:b[6],platformDepth:b[7]}));}
export function documentFor(layout){return {schema:'math-refuge-layout',version:1,units:'metres',origin:'original-01A-centre',axes:{east:'+X',north:'-Z'},savedAt:new Date().toISOString(),buildings:snapshot(layout)};}
export function validateDocument(doc,layout){
 if(doc?.schema!=='math-refuge-layout'||![1,2].includes(doc.version)||doc.units!=='metres'||doc.origin!=='original-01A-centre'||doc.axes?.east!=='+X'||doc.axes?.north!=='-Z')throw Error('布局格式或坐标系不匹配');
 if(!Array.isArray(doc.buildings)||doc.buildings.length!==layout.length)throw Error('建筑数量不匹配');
 const seen=new Set();
 for(const b of doc.buildings){if(!layout.some(a=>a[0]===b.id)||seen.has(b.id))throw Error('建筑编号重复或未知');seen.add(b.id);if(![b.east,b.north].every(n=>typeof n==='number'&&Number.isFinite(n)&&Math.abs(n)<=10000))throw Error('坐标须在 ±10000 米范围内');}
 return doc.buildings;
}
