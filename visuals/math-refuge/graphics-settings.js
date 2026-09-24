export const GRAPHICS_PRESETS={
 balanced:{quality:'balanced',resolutionScale:'100',shadowQuality:'1024',cloudQuality:'low',textureFiltering:'8',waterDetail:'low',waterReflection:'simple'},
 high:{quality:'high',resolutionScale:'100',shadowQuality:'2048',cloudQuality:'medium',textureFiltering:'16',waterDetail:'high',waterReflection:'full'},
 ultra:{quality:'ultra',resolutionScale:'125',shadowQuality:'4096',cloudQuality:'high',textureFiltering:'16',waterDetail:'high',waterReflection:'full'}
};
export const CLOUD_LEVELS={low:{size:256,steps:16,interval:400},medium:{size:512,steps:24,interval:250},high:{size:1024,steps:32,interval:160}};
export function recommendedGraphics({mobile=false,gpu='',maxTextureSize=4096}={}){
 // Model names only supply a safe initial choice; measured GPU time controls adaptation.
 const high=!mobile&&maxTextureSize>=8192&&!/Intel|SwiftShader|llvmpipe/i.test(gpu);
 return {...GRAPHICS_PRESETS[high?'high':'balanced'],resolutionScale:high?'125':'100',targetFPS:'60',adaptiveQuality:'auto',rainEffects:'on',starEffects:mobile?'off':'on',geometryDetail:'auto',windWaves:'on',waveStrength:'50',sunReflection:'on'};
}
export function resolutionRatio(base,scale,width,height,maxTextureSize=8192){
 return Math.max(.25,Math.min(base*Number(scale)/100,maxTextureSize/Math.max(width,height),Math.sqrt(8500000/(width*height))));
}
export function sunWaterVisibility(height,radius){const t=Math.max(0,Math.min(1,(height+radius)/(2*radius)));return t*t*(3-2*t);}
