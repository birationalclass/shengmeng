import test from 'node:test';
import assert from 'node:assert/strict';
import {ShaderChunk} from '../3d/vendor/three.module.js';
import {optimizeLocalLights,localLightPars,localLightFragment} from './local-light-shader.js';
test('finite light rejection preserves unbounded lamps and guards every direct BRDF',()=>{
 for(const name of ['pointLight','spotLight']){
  assert(localLightPars.includes(`${name}.distance > 0.0 && lightDistanceSquared >= ${name}.distance * ${name}.distance`));
 }
 const calls=ShaderChunk.lights_fragment_begin.match(/RE_Direct\( directLight/g).length;
 assert.equal((localLightFragment.match(/if \( directLight.visible \) \{ RE_Direct/g)||[]).length,calls);
 assert(localLightPars.includes('getDistanceAttenuation( lightDistance, pointLight.distance, pointLight.decay )'),'Original in-range attenuation is preserved');
 assert(localLightPars.includes('getSpotAttenuation( spotLight.coneCos, spotLight.penumbraCos, angleCos )'));
 const shader={fragmentShader:'#include <lights_pars_begin>\n#include <lights_fragment_begin>\n#include <lights_fragment_maps>'};
 optimizeLocalLights(shader);assert(!shader.fragmentShader.includes('#include <lights_fragment_begin>'));
 assert(shader.fragmentShader.includes('#include <lights_fragment_maps>'),'Indirect lighting stays intact');
 assert(!ShaderChunk.lights_fragment_begin.includes('if ( directLight.visible ) { RE_Direct'),'Vendor chunks are never mutated');
});
