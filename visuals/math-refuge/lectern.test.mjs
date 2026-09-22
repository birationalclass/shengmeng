import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import vm from 'node:vm';
import * as T from '../3d/vendor/three.module.js';
import {createLectern} from './lectern.js';
import {bindPhysicalButtons} from './physical-buttons.js';

test('lectern touch surfaces raycast, cancel drags and redraw only on state changes',()=>{
  globalThis.document={createElement:()=>({getContext:()=>({fillRect(){},fillText(){}})})};
  const l=createLectern(T);l.group.updateMatrixWorld(true);
  try{
    const display=l.group.getObjectByName('Embedded anti-glare touch display'),tex=display.material.map;
    l.update({playing:true,page:3,total:20});const version=tex.version;l.update({playing:true,page:3,total:20});assert.equal(tex.version,version);
    const pad=l.targets.find(o=>o.userData.action==='lectern:play'),position=pad.getWorldPosition(new T.Vector3()),normal=new T.Vector3(0,0,1).transformDirection(pad.matrixWorld);
    const ray=new T.Raycaster(position.clone().addScaledVector(normal,.5),normal.clone().negate());assert.equal(ray.intersectObjects(l.targets,false)[0].object,pad);
    pad.userData.hovered=true;l.update({playing:true,page:3,total:20});assert(tex.version>version);
    const events={},actions=[],canvas={addEventListener(k,f){events[k]=f;},removeEventListener(){},style:{}},controls={enabled:true};
    const binding=bindPhysicalButtons(canvas,controls,()=>pad,a=>actions.push(a));
    const e=x=>({button:0,pointerId:1,clientX:x,clientY:0,preventDefault(){},stopImmediatePropagation(){}});
    events.pointerdown(e(0));events.pointerup(e(30));assert.deepEqual(actions,[]);assert(controls.enabled);
    events.pointerdown(e(0));events.pointerup(e(0));assert.deepEqual(actions,['lectern:play']);binding.dispose();
    const body=l.group.getObjectByName('Tapered graphite spine');assert.equal(body.userData.action,'lectern:view');
    let triangles=0;l.group.traverse(o=>{if(o.geometry)triangles+=(o.geometry.index?.count||o.geometry.attributes.position.count)/3;});assert(triangles<15000);
  }finally{l.dispose();delete globalThis.document;}
});

test('speaker view remains manual through idle time and exits only on explicit camera selection',async()=>{
  const app=await fs.readFile(new URL('./app.js',import.meta.url),'utf8');
  const names=['enterSpeakerView','selectShot','resumeTour'];
  const definitions=names.map(name=>app.match(new RegExp('function '+name+'\\([^]*?\\n\\}'))[0]).join('\n');
  const context=vm.createContext({keys:new Set(['w']),reader:{close(){}},boardFollow:{reset(){}},beginTransition(){},updateLabels(){},opening:{},choosingReport:true,speakerView:false,touring:true,free:false});
  vm.runInContext(definitions+';enterSpeakerView();',context);
  assert(context.speakerView);assert(!context.touring);assert(context.free);assert.equal(context.opening,null);assert.equal(context.keys.size,0);
  assert(app.includes('!speakerView&&SHOTS[shot].lecture&&lecture&&boardFollow.following'));
  vm.runInContext('selectShot(4)',context);assert(!context.speakerView);
  vm.runInContext('enterSpeakerView();resumeTour()',context);assert(!context.speakerView);assert(context.touring);
});
