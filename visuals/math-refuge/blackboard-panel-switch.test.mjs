import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import * as T from '../3d/vendor/three.module.js';
import {batchLectureGeometry} from './blackboard-lecture-batching.js';
import {boardHeights,boardSlot,BOARD_LAYOUT} from './lecture-state.js';
test('panel-local batching preserves frame and writing face transforms during the lift',()=>{
 const root=new T.Group(),material=new T.MeshBasicMaterial(),panels=[];
 for(let pair=0;pair<3;pair++)for(let side=0;side<2;side++){
  const group=new T.Group();group.name=`Sliding chalkboard ${pair+1}${side?'B':'A'}`;group.position.set(pair*5.6,boardHeights(0)[side],0);root.add(group);panels.push(group);
  for(const x of [-2,2]){const frame=new T.Mesh(new T.BoxGeometry(.1,2,.1),material);frame.position.x=x;group.add(frame);}
  const face=new T.Mesh(new T.PlaneGeometry(5,2),new T.MeshBasicMaterial());face.name='Matte writing face';group.add(face);
 }
 const result=batchLectureGeometry(T,root);assert.equal(result.movingPanels,6);assert.equal(result.panelLocalBatches,6);
 for(let i=0;i<6;i++){const group=panels[i];assert.equal(group.parent,root);assert(group.children.some(o=>o.name==='Matte writing face'));assert(group.children.some(o=>o.name.startsWith('Batched auditorium')));assert(group.matrixAutoUpdate);}
 const old=panels[1].children.map(o=>o.getWorldPosition(new T.Vector3()).y);panels[1].position.y=BOARD_LAYOUT.low;root.updateMatrixWorld(true);panels[1].children.forEach((o,i)=>assert(Math.abs(o.getWorldPosition(new T.Vector3()).y-old[i]-(BOARD_LAYOUT.low-BOARD_LAYOUT.high))<1e-8));
});
test('six physical panels cycle by column and return the selected panel to working height',()=>{
 for(let page=0;page<12;page++){const slot=boardSlot(page),heights=boardHeights(slot%2);assert.equal(slot,page%6);assert.equal(heights[slot%2],BOARD_LAYOUT.low);assert.equal(heights[1-slot%2],BOARD_LAYOUT.high);}
 const source=readFileSync(new URL('./blackboard-app.js',import.meta.url),'utf8');assert(source.includes('fixedBoards:false'));assert(source.includes('batchLectureGeometry(T,lectureRoot)'));assert(!source.includes('fixedBoards:true'));
});
