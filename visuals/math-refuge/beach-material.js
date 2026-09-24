import * as THREE from 'three';
export function createBeachMaterial(seaLevel){
 const clock={value:0},material=new THREE.MeshStandardMaterial({color:'#d9c596',roughness:.94});
 material.onBeforeCompile=shader=>{
 shader.uniforms.sandTime=clock;shader.uniforms.sandSea={value:seaLevel};
 shader.vertexShader='varying vec3 sandWorld;\n'+shader.vertexShader.replace('#include <begin_vertex>','#include <begin_vertex>\nsandWorld=(modelMatrix*vec4(transformed,1.)).xyz;');
 shader.fragmentShader=`varying vec3 sandWorld;uniform float sandTime,sandSea;
 float sandHash(vec2 p){return fract(sin(dot(p,vec2(127.1,311.7)))*43758.5453);}
 float sandNoise(vec2 p){vec2 i=floor(p),f=fract(p);f=f*f*(3.-2.*f);return mix(mix(sandHash(i),sandHash(i+vec2(1,0)),f.x),mix(sandHash(i+vec2(0,1)),sandHash(i+vec2(1,1)),f.x),f.y);}
 `+shader.fragmentShader;
 shader.fragmentShader=shader.fragmentShader.replace('#include <color_fragment>',`#include <color_fragment>
 float sandHeight=sandWorld.y-sandSea;
 float runup=.035*(1.+sin(sandTime*.49+sandWorld.x*.11+sandWorld.z*.13));
 float damp=1.-smoothstep(.02+runup,.40+runup,sandHeight);
 float patches=sandNoise(sandWorld.xz*.37)*.6+sandNoise(sandWorld.xz*1.7)*.4;
 float grain=sandNoise(sandWorld.xz*62.);
 float grainFade=1./(1.+80.*max(length(dFdx(sandWorld.xz)),length(dFdy(sandWorld.xz))));
 diffuseColor.rgb*=mix(1.,.62,damp)*(.94+.12*patches+(grain-.5)*.18*grainFade);
 `).replace('#include <roughnessmap_fragment>','#include <roughnessmap_fragment>\nroughnessFactor=mix(.94,.32,damp);');
 };
 material.customProgramCacheKey=()=> 'sand-dry-wet-v89';
 return {material,update(dt){clock.value+=Math.max(0,Math.min(.1,dt));}};
}
