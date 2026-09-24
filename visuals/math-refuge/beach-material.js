import * as THREE from 'three';
export function createBeachMaterial(seaLevel){
 const clock={value:0},material=new THREE.MeshStandardMaterial({color:'#c9b88f',roughness:.94});
 material.onBeforeCompile=shader=>{
 shader.uniforms.sandTime=clock;shader.uniforms.sandSea={value:seaLevel};
 shader.vertexShader='varying vec3 sandWorld;\n'+shader.vertexShader.replace('#include <begin_vertex>','#include <begin_vertex>\nsandWorld=(modelMatrix*vec4(transformed,1.)).xyz;');
 shader.fragmentShader=`varying vec3 sandWorld;uniform float sandTime,sandSea;
 float sandHash(vec2 p){return fract(sin(dot(p,vec2(127.1,311.7)))*43758.5453);}
 float sandNoise(vec2 p){vec2 i=floor(p),f=fract(p);f=f*f*(3.-2.*f);return mix(mix(sandHash(i),sandHash(i+vec2(1,0)),f.x),mix(sandHash(i+vec2(0,1)),sandHash(i+vec2(1,1)),f.x),f.y);}
 `+shader.fragmentShader;
 shader.fragmentShader=shader.fragmentShader.replace('#include <color_fragment>',`#include <color_fragment>
 float sandHeight=sandWorld.y-sandSea;
 // Wet sand persists above the moving water; do not paint a second moving edge.
 float runup=.15;
 float film=1.-smoothstep(-.03,.015,sandHeight);
 float washEdge=0.;
 float patches0=sandNoise(sandWorld.xz*.19);
 float damp=1.-smoothstep(.02+runup,.48+runup,sandHeight+(patches0-.5)*.09);
 float patches=sandNoise(sandWorld.xz*.37)*.6+sandNoise(sandWorld.xz*1.7)*.4;
 float footprint=max(length(dFdx(sandWorld.xz)),length(dFdy(sandWorld.xz)));
 // Separate mineral flecks and millimetre grains, filtered before they alias.
 float coarseFade=1.-smoothstep(.018,.09,footprint);
 float fineFade=1.-smoothstep(.0015,.012,footprint);
 float grain=sandNoise(sandWorld.xz*85.);
 float fine=sandNoise(sandWorld.xz*420.);
 float mineral=sandHash(floor(sandWorld.xz*93.));
 float fleck=(smoothstep(.82,.97,mineral)*.24-smoothstep(.72,.93,1.-mineral)*.30)*coarseFade;
 float sandRelief=(grain-.5)*.006*coarseFade+(fine-.5)*.0017*fineFade;
 sandRelief*=mix(1.,.35,damp);
 float grainFade=coarseFade;

 diffuseColor.rgb*=mix(1.,.57,damp)*(.94+.12*patches+(grain-.5)*.30*grainFade+fleck+(fine-.5)*.13*fineFade);
  diffuseColor.rgb=mix(diffuseColor.rgb,diffuseColor.rgb*vec3(.74,.87,.90),film*.18);
 diffuseColor.rgb+=vec3(.10,.12,.11)*washEdge;
 `).replace('#include <normal_fragment_maps>',`#include <normal_fragment_maps>
 vec3 sandQ0=dFdx(-vViewPosition),sandQ1=dFdy(-vViewPosition);
 vec3 sandR1=cross(sandQ1,normal),sandR2=cross(normal,sandQ0);
 float sandDet=dot(sandQ0,sandR1);
 normal=normalize(abs(sandDet)*normal-sign(sandDet)*(dFdx(sandRelief)*sandR1+dFdy(sandRelief)*sandR2));
 `).replace('#include <roughnessmap_fragment>','#include <roughnessmap_fragment>\nroughnessFactor=mix(mix(.94,.42,damp),.19,film);');
 };
 material.customProgramCacheKey=()=> 'sand-granular-v98';
 return {material,update(dt){clock.value+=Math.max(0,Math.min(.1,dt));}};
}
