import test from 'node:test';
import assert from 'node:assert/strict';
import * as T from '../../3d/vendor/three.module.js';
import {SudokuAtlas} from '../atlas.mjs';
import {PLACES} from '../journey.mjs';

test('both drawbridge leaves lower from above and meet at the centre',()=>{
 for(let i=0;i<7;i++){
  const a=PLACES[i],b=PLACES[i+1],length=Math.hypot(b[0]-a[0],b[1]-a[1])-26.2;
  const g=new T.Group();g.position.set((a[0]+b[0])/2,0,(a[1]+b[1])/2);g.rotation.y=Math.atan2(b[0]-a[0],b[1]-a[1]);
  const leaves=[-1,1].map(sign=>{const p=new T.Group();p.position.set(0,.25,sign*length/2);p.rotation.y=sign===1?Math.PI:0;p.userData.bridgeSide=sign;g.add(p);return p;});
  const state={bridges:[{g,leaves,chains:[],length}],bridgeProgress:[0]};let previous=Infinity;
  for(const u of [0,.01,.25,.5,.75,1]){
   state.bridgeProgress[0]=u;SudokuAtlas.prototype.updateBridges.call(state);
   const tips=leaves.map(p=>p.localToWorld(new T.Vector3(0,0,length/2)));
   for(const tip of tips){assert.ok(tip.y>=.25-1e-9);assert.ok(tip.y<=previous+1e-9);}
   assert.ok(Math.abs(tips[0].y-tips[1].y)<1e-9);previous=tips[0].y;
   if(u===1)assert.ok(tips[0].distanceTo(tips[1])<1e-9);
  }
 }
});
