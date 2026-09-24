// A bounded diffuse-irradiance approximation for reflected seminar-room light.
// It lights material colour (not emission), with a soft boundary outside the room.
import {optimizeLocalLights} from './local-light-shader.js?v81-imac';
export function createRoomFill(){
  const strength={value:0},seen=new WeakSet();
  function apply(root){root.traverse(object=>{
    for(const material of Array.isArray(object.material)?object.material:[object.material]){
      if(!material?.isMeshStandardMaterial||seen.has(material))continue;
      seen.add(material);const prior=material.onBeforeCompile,priorKey=material.customProgramCacheKey();
      material.onBeforeCompile=function(shader,renderer){
        prior.call(this,shader,renderer);optimizeLocalLights(shader);shader.uniforms.seminarFill=strength;
        shader.vertexShader='varying vec3 seminarWorld;\n'+shader.vertexShader;
        shader.vertexShader=shader.vertexShader.replace('#include <project_vertex>',`#include <project_vertex>
          vec4 seminarVertex=vec4(transformed,1.0);
          #ifdef USE_INSTANCING
            seminarVertex=instanceMatrix*seminarVertex;
          #endif
          seminarWorld=(modelMatrix*seminarVertex).xyz;`);
        shader.fragmentShader='varying vec3 seminarWorld;\nuniform float seminarFill;\n'+shader.fragmentShader;
        shader.fragmentShader=shader.fragmentShader.replace('#include <lights_fragment_maps>',`#include <lights_fragment_maps>
          #if defined(RE_IndirectDiffuse)
            vec3 outside=max(max(vec3(49.2,0.35,-14.1)-seminarWorld,seminarWorld-vec3(61.2,5.35,14.1)),vec3(0.0));
            float roomMask=1.0-smoothstep(0.0,1.1,length(outside));
            vec3 seminarOutside=max(max(vec3(-124.5,0.35,2.8)-seminarWorld,seminarWorld-vec3(-113.0,12.55,19.8)),vec3(0.0));
            roomMask=max(roomMask,1.0-smoothstep(0.0,0.8,length(seminarOutside)));
            irradiance+=vec3(1.0,0.89,0.75)*seminarFill*roomMask;
          #endif`);
      };
      material.customProgramCacheKey=()=>priorKey+'-seminar-diffuse-v3-local-lights';material.needsUpdate=true;
    }
  });}
  return {strength,apply,setDaylight(day){strength.value=.18+(1-day)*2.1;}};
}
