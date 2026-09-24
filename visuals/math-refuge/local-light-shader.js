import {ShaderChunk} from '../3d/vendor/three.module.js';

// Three's forward shader evaluates the physical BRDF even when a finite-range
// lamp contributes exactly zero. Reject those fragments before the BRDF. This
// preserves all lamps and their original intensity, range and cone falloff.
const rangeGuard=`
  float lightDistanceSquared = dot( lVector, lVector );
  if ( LIGHT.distance > 0.0 && lightDistanceSquared >= LIGHT.distance * LIGHT.distance ) {
    light.color = vec3( 0.0 ); light.direction = vec3( 0.0, 1.0, 0.0 ); light.visible = false; return;
  }`;
export const localLightPars=ShaderChunk.lights_pars_begin
 .replace('vec3 lVector = pointLight.position - geometryPosition;', 'vec3 lVector = pointLight.position - geometryPosition;'+rangeGuard.replaceAll('LIGHT','pointLight'))
 .replace('vec3 lVector = spotLight.position - geometryPosition;', 'vec3 lVector = spotLight.position - geometryPosition;'+rangeGuard.replaceAll('LIGHT','spotLight'));
export const localLightFragment=ShaderChunk.lights_fragment_begin.replaceAll(
 'RE_Direct( directLight, geometryPosition, geometryNormal, geometryViewDir, geometryClearcoatNormal, material, reflectedLight );',
 'if ( directLight.visible ) { RE_Direct( directLight, geometryPosition, geometryNormal, geometryViewDir, geometryClearcoatNormal, material, reflectedLight ); }');
export function optimizeLocalLights(shader){
 shader.fragmentShader=shader.fragmentShader.replace('#include <lights_pars_begin>',localLightPars).replace('#include <lights_fragment_begin>',localLightFragment);
}
