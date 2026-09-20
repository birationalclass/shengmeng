import * as T from '../3d/vendor/three.module.js';
export const BUILD_TIME_KEY='group-sudoku-build-seconds';
export const DEFAULT_BUILD_SECONDS=15;
export const BOARD_RISE_SECONDS=1.2;
export function buildSeconds(value){const n=Number(value);return value===null||value===undefined||!Number.isFinite(n)?15:Math.max(5,Math.min(45,n));}
export function readBuildSeconds(storage){try{return buildSeconds(storage?.getItem(BUILD_TIME_KEY));}catch{return 15;}}
export function riseProgress(u,twoStep=false){u=Math.max(0,Math.min(1,u));const ease=v=>v*v*(3-2*v);if(!twoStep)return ease(u);return u<.40?.5*ease(u/.40):u<.58?.5:.5+.5*ease((u-.58)/.42);}
function order(name,height,z){if(/paving|floor|foundation|pool-wall|pool-rim|pool.*edge|coping|seal/.test(name)||height<.4)return 0;if(/water-court|pool-water|lake/.test(name))return 1;if(/steam-power|imperial|ice-palace|dominant|great-hall/.test(name))return 2;if(/clock|transmission-wall|tower|temple|pagoda|spire|keep|chess-king|chess-queen/.test(name))return 3;if(/hoist|gallery|study|bridge|wall|pavilion|chess/.test(name))return 4;if(/owl|skater|boat|tree|lantern|swan/.test(name))return 6;return z<0?3:5;}
export function planConstruction(content,lift,atlas={}){
 content.updateWorldMatrix(true,true);const candidates=[];
 const dynamic=new Set([...(atlas.rotating||[]).map(m=>m.object),...(atlas.detailMotion||[]).map(m=>m.object),...(atlas.iceSkaters||[]).map(m=>m.root),...(atlas.owls||[]).map(m=>m.root),...(atlas.poolBoats||[]).map(m=>m.root),...(atlas.machineMotion||[]).map(m=>m.root),...Object.values(atlas.clockHands||{})]);
 function collect(o){if(o===lift)return;if(dynamic.has(o)){candidates.push(o);return;}if(o.isMesh){candidates.push(o);return;}if(o.isLine||o.isPoints)return;
  // Long walls are assembled segment by segment; other named buildings stay rigid.
  if(o.userData.landmark&&o.userData.landmark!=='great-wall'){candidates.push(o);return;}
  const children=[...o.children];if(!o.userData.landmark&&children.some(c=>c.isMesh)&&o!==content&&o.parent?.userData.landmark==='great-wall'){candidates.push(o);return;}
  children.forEach(collect);
 }
 [...content.children].forEach(collect);
 const inverse=content.matrixWorld.clone().invert(),buckets=new Map();
 for(const object of candidates){const box=new T.Box3().setFromObject(object),center=box.getCenter(new T.Vector3()).applyMatrix4(inverse),height=box.max.y-box.min.y,name=object.userData.landmark||'',rank=order(name,height,center.z);
  // Flat paving is one early stage. Unnamed structural details follow their region.
  const sector=Math.round(Math.atan2(center.x,center.z)*4/Math.PI),key=object.isMesh?`${object.parent.uuid}:${rank}:${rank===0?'floor':sector}`:object.uuid;
  if(!buckets.has(key))buckets.set(key,{objects:[],name,rank,z:center.z,x:center.x,height:0});const b=buckets.get(key);b.objects.push(object);b.height=Math.max(b.height,height);
 }
 const groups=[...buckets.values()].sort((a,b)=>a.rank-b.rank||a.z-b.z||a.x-b.x),parts=[];
 for(const [i,b]of groups.entries()){
  const wrapper=new T.Group(),parent=b.objects[0].parent;wrapper.name='construction:'+b.name;parent.add(wrapper);for(const object of b.objects)wrapper.add(object);const inverseParent=parent.matrixWorld.clone().invert(),direction=new T.Vector3(0,1,0).applyMatrix4(inverseParent).sub(new T.Vector3().applyMatrix4(inverseParent));
  const twoStep=b.height>2.7&&/clock|hall|tower|temple|pagoda|palace|hoist|spire|keep|transmission/.test(b.name);
  parts.push({object:wrapper,position:wrapper.position.clone(),scale:wrapper.scale.clone(),rigid:true,decoration:true,twoStep,direction,lift:Math.max(.65,Math.min(8,b.height+.35)),order:i,count:groups.length,name:b.name});
 }
 parts.push({object:lift,position:lift.position.clone(),scale:lift.scale.clone(),rigid:true,board:true,lift:2.2});
 return parts;
}
export function constructionTiming(part,seconds=15){if(part.board)return {delay:seconds+.15,duration:BOARD_RISE_SECONDS};if(!part.decoration)return {delay:part.delay,duration:part.duration};const duration=Math.min(seconds*.3,part.twoStep?2.6:1.05);return {delay:part.order/Math.max(1,part.count-1)*(seconds-duration),duration};}
