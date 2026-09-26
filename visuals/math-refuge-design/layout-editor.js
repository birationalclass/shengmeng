import {bridgePlan} from './bridge-plan-preset.js';
import {STORAGE_KEY,snapshot,documentFor,validateDocument} from './layout-data.js';
export function installLayoutEditor({bar,layout,members,sharedVertices,scene,focus,stop,onMove,design}){
 const editor=document.createElement('section');editor.id='layoutEditor';
 editor.innerHTML=`<h2>手动调整布局</h2>
 <label for="layoutSelect">调整对象</label><select id="layoutSelect"><option value="all">全部建筑群落（含住宅）</option>${layout.map(b=>`<option value="${b[0]}">${b[0]} ${b[1]}</option>`).join('')}</select>
 <div class="positionFields"><label>东向 X / 米<input id="layoutEast" type="number" step="0.1" min="-10000" max="10000"></label><label>北向 Y / 米<input id="layoutNorth" type="number" step="0.1" min="-10000" max="10000"></label></div>
 <div><button id="layoutApply">应用坐标</button><button id="layoutFocus">定位所选</button></div>
 <label>移动步长 / 米<select id="layoutStep"><option value="1">1 米</option><option value="5">5 米</option><option value="10" selected>10 米 / 1 格</option><option value="0.1">0.1 米</option></select></label>
 <div class="movePad"><button data-move="0,1">向北 ↑</button><button data-move="-1,0">向西 ←</button><button data-move="1,0">向东 →</button><button data-move="0,-1">向南 ↓</button></div>
 <div><button id="layoutUndo">撤销上一步</button><button id="layoutSave">保存布局</button><button id="layoutExport">导出 JSON</button><button id="layoutImport">导入 JSON</button></div>
 <input type="file" id="layoutFile" accept=".json,application/json" hidden>
 <p id="layoutSaveStatus" role="status"></p><p id="layoutWarning"></p>
 <details><summary>查看当前布局数据</summary><textarea id="layoutJson" readonly aria-label="当前布局JSON数据" rows="7"></textarea></details>
 <small>保存到当前浏览器；下次打开自动恢复。导出 JSON 可备份并交给我继续设计。连桥与附属物跟随，海岸不移动。</small>`;
 bar.append(editor);
 const $=id=>editor.querySelector('#'+id),select=$('layoutSelect'),east=$('layoutEast'),north=$('layoutNorth'),status=$('layoutSaveStatus'),history=[];
 let dirty=false;
 const baseLayout=layout.slice();
 const doc=()=>({...documentFor(layout),...design.serialize()});
 const remember=()=>{history.push(doc());if(history.length>50)history.shift();};
 function restore(value){design.validate(value);const combined=[...baseLayout,...(value.assets||[]).map(a=>[a.id])];const rows=validateDocument(value,combined);design.restore(value);apply(rows,false);}
 function changed(){dirty=true;status.textContent='有未保存的调整';refresh();}
 design.bind({remember,changed,move:rows=>apply(rows,false),select:id=>{refresh();select.value=id;refresh();}});

 function refresh(){
  const prior=select.value;select.replaceChildren(new Option('全部建筑群落（含住宅）','all'),...layout.map(b=>new Option(b[0]+' '+b[1],b[0])));select.value=layout.some(b=>b[0]===prior)?prior:'all';
  const b=layout.find(a=>a[0]===select.value),all=!b;
  east.disabled=north.disabled=$('layoutApply').disabled=all;east.value=b?b[4]:'';north.value=b?b[5]:'';
  $('layoutFocus').textContent=all?'查看总览':'定位所选';$('layoutUndo').disabled=!history.length;
  $('layoutJson').value=JSON.stringify(doc(),null,2);
  const hall=layout.find(b=>b[0]==='01B'),warnings=[];
  for(const b of layout.filter(b=>!['01B','10'].includes(b[0]))){const west=hall[4]-hall[6]/2+15.27;const farX=b[4]-b[6]/2;if(farX<west&&Math.abs(b[5]-hall[5])-b[7]/2<16.27+west-farX)warnings.push(b[0]);}
  const overlaps=[];for(let i=0;i<layout.length;i++)for(let j=i+1;j<layout.length;j++){const a=layout[i],b=layout[j];if(Math.abs(a[4]-b[4])<(a[6]+b[6])/2&&Math.abs(a[5]-b[5])<(a[7]+b[7])/2)overlaps.push(a[0]+'/'+b[0]);}
  $('layoutWarning').textContent=[warnings.length?'日落通廊可能被占用：'+warnings.join('、'):'',overlaps.length?'平台包络重叠：'+overlaps.join('、'):''].filter(Boolean).join('；');
 }
 function apply(rows,remember=true){
  if(remember){history.push(doc());if(history.length>50)history.shift();}
  stop();
  const changedGeometry=new Set();
  for(const row of rows){const b=layout.find(a=>a[0]===row.id);if(!b)continue;const dx=row.east-b[4],dy=row.north-b[5];
   for(const obj of members.get(b[0])||[]){obj.position.x+=dx;obj.position.z-=dy;obj.updateMatrixWorld(true);}
   for(const part of sharedVertices.filter(p=>p.id===b[0])){const p=part.geometry.attributes.position;for(const i of part.indices)p.setXYZ(i,p.getX(i)+dx/part.scale,p.getY(i),p.getZ(i)-dy/part.scale);p.needsUpdate=true;changedGeometry.add(part.geometry);}
   b[4]=row.east;b[5]=row.north;
  }
  for(const g of changedGeometry){g.computeBoundingBox();g.computeBoundingSphere();}
  scene.updateMatrixWorld(true);onMove();dirty=true;status.textContent='有未保存的调整';refresh();
 }
 function move(dx,dy){const rows=snapshot(layout).filter(b=>select.value==='all'||b.id===select.value).map(b=>({...b,east:Math.round((b.east+dx)*1000)/1000,north:Math.round((b.north+dy)*1000)/1000}));if(rows.some(b=>Math.abs(b.east)>10000||Math.abs(b.north)>10000)){status.textContent='坐标须在 ±10000 米范围内';return;}apply(rows);}
 select.onchange=()=>{refresh();design.select(select.value);};
 editor.querySelectorAll('[data-move]').forEach(button=>button.onclick=()=>{const [x,y]=button.dataset.move.split(',').map(Number),step=Number($('layoutStep').value);move(x*step,y*step);});
 $('layoutApply').onclick=()=>{const b=layout.find(a=>a[0]===select.value),x=east.valueAsNumber,y=north.valueAsNumber;if(!b||![x,y].every(n=>Number.isFinite(n)&&Math.abs(n)<=10000)){status.textContent='请输入有效坐标（±10000 米）';return;}apply([{id:b[0],east:x,north:y}]);};
 $('layoutFocus').onclick=()=>focus(select.value==='all'?'all':select.value);
 $('layoutUndo').onclick=()=>{if(history.length)restore(history.pop());};
 function save(){try{localStorage.setItem(STORAGE_KEY,JSON.stringify(doc()));dirty=false;status.textContent='已保存至本机浏览器 · '+new Date().toLocaleTimeString();return true;}catch{status.textContent='浏览器保存失败，请导出 JSON 备份';return false;}}
 $('layoutSave').onclick=save;
 $('layoutExport').onclick=()=>{const text=JSON.stringify(doc(),null,2),url=URL.createObjectURL(new Blob([text],{type:'application/json'})),a=document.createElement('a');a.href=url;a.download='math-refuge-layout-'+new Date().toISOString().slice(0,10)+'.json';a.click();setTimeout(()=>URL.revokeObjectURL(url),10000);save();};
 $('layoutImport').onclick=()=>$('layoutFile').click();
 $('layoutFile').onchange=async e=>{try{const file=e.target.files[0];if(!file)return;if(file.size>2000000)throw Error('文件过大');const value=JSON.parse(await file.text());design.validate(value);validateDocument(value,[...baseLayout,...(value.assets||[]).map(a=>[a.id])]);remember();restore(value);status.textContent='已导入，可继续调整；点击保存后生效';}catch(err){status.textContent='导入失败：'+err.message;}finally{e.target.value='';}};
 // Versioned key makes the 30m shift a one-time baseline, never cumulative on reload.
 let saved=null;try{const text=localStorage.getItem(STORAGE_KEY);if(text){saved=JSON.parse(text);design.validate(saved);validateDocument(saved,[...baseLayout,...(saved.assets||[]).map(a=>[a.id])]);}}catch{saved=null;status.textContent='已保存数据无法读取，使用东移30米初始布局';}
 if(new URLSearchParams(location.search).get('plan')==='bridges-20260926'){restore(bridgePlan);dirty=false;status.textContent='已载入你的布局及连桥方案 · 可继续调整并保存';}
 else if(saved){restore(saved);dirty=false;status.textContent='已恢复上次保存的布局';}
 else {design.restore({version:1});apply(snapshot(layout).map(b=>({...b,east:b.east+30})),false);save();status.textContent='初始布局已整体向东 30 米（3 格），并保存';}
 history.length=0;refresh();
 window.addEventListener('beforeunload',e=>{if(dirty){e.preventDefault();e.returnValue='';}});
}
