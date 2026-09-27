import {test} from 'node:test';
import assert from 'node:assert/strict';
import {StartupQuality} from './startup-quality.js';
const desired={quality:'high',resolutionScale:'100',cloudQuality:'medium',shadowQuality:'2048',oceanModel:'auto',adaptiveQuality:'auto'};
function run(q,ms,count,start=0){for(let i=0;i<count;i++)q.sample(ms,start+i*ms);}
test('begins with shadows and volumetric clouds off; stable measured frames promote one tier at a time',()=>{
 const q=new StartupQuality();assert.equal(q.settings(desired).shadowQuality,'0');assert.equal(q.settings(desired).resolutionScale,'75');
 run(q,1000/60,290);assert.equal(q.level,1);assert.equal(q.settings(desired).shadowQuality,'0');
 run(q,1000/60,300,5000);assert.equal(q.level,2);assert.deepEqual(q.settings(desired),desired);
});
test('30fps hardware stays cheap; slow frames after promotion back off and do not immediately retry',()=>{
 const q=new StartupQuality();run(q,1000/30,600);assert.equal(q.level,0);
 run(q,1000/60,360,21000);assert.equal(q.level,1);run(q,1000/30,100,27000);assert.equal(q.level,0);
 run(q,1000/60,600,31000);assert.equal(q.level,0);
});
test('hidden-tab gaps do not count as good calibration frames',()=>{const q=new StartupQuality();run(q,16.67,150);q.sample(60000,70000);assert.equal(q.good,0);assert.equal(q.level,0);});

test('smart quality stays enabled after warmup even when old preferences were fixed',()=>{const q=new StartupQuality();q.level=2;const settings=q.settings({...desired,adaptiveQuality:'fixed',oceanModel:'study'});assert.equal(settings.adaptiveQuality,'auto');assert.equal(settings.oceanModel,'auto');});
