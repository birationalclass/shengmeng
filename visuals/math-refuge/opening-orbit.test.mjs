import test from 'node:test';import assert from 'node:assert/strict';import vm from 'node:vm';import {readFile} from 'node:fs/promises';
const source=await readFile(new URL('./app.js',import.meta.url),'utf8');
const select=source.slice(source.indexOf('function selectShot('),source.indexOf('function resumeTour('));
test('opening keeps its sunrise endpoint; explicit hall selection enables its orbit',()=>{
 const c={cameraLocked:()=>false,sunriseIntro:{waiting:false},SHOTS:[{name:'报告厅',hallOrbit:true}],boardFollow:{reset(){}},beginTransition(){c.blend={};},updateLabels(){},setSeminarPanel(){},buildingForShot(){return {};}};
 vm.createContext(c);vm.runInContext(select,c);
 c.selectShot(0,false,true);assert.equal(c.free,true);assert.equal(c.blend.openingArrival,true);
 c.selectShot(0,false,false);assert.equal(c.free,false);assert.equal(c.blend.openingArrival,false);
});
