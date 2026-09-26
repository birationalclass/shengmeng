import test from 'node:test';
import assert from 'node:assert/strict';
import * as T from '../3d/vendor/three.module.js';
import {createAutomaticDoors} from './automatic-doors.js';
test('predicted flight opens transformed door without hover; another floor stays closed',()=>{
 const scene=new T.Group(),m=new T.MeshBasicMaterial(),doors=createAutomaticDoors(T,m,m);
 const g=doors.add(scene,{x:20,y:0,z:4,width:2,height:3,axis:'z',name:'west'});
 scene.scale.setScalar(1.4);scene.updateMatrixWorld(true);
 const path=[g.localToWorld(new T.Vector3(0,0,12)),g.localToWorld(new T.Vector3(0,0,-2))];
 for(let i=0;i<15;i++)doors.update(.1,false,path);
 assert(doors.doors[0].opening>.99);
 const above=path.map(p=>p.clone().add(new T.Vector3(0,10,0)));
 for(let i=0;i<70;i++)doors.update(.1,false,above);
 assert(doors.doors[0].opening<.001);
 doors.targets[0].userData.hovered=true;doors.update(.1,true);assert.equal(doors.doors[0].opening,1);
 doors.dispose();m.dispose();
});
