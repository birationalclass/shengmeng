// Bennett apparent-altitude refraction, standard atmosphere; no inversion-layer mirage.
const rad=Math.PI/180;
export function refractionDegrees(apparent){const h=Math.max(-.5,Math.min(89.9,apparent));return Math.max(0,1/Math.tan((h+7.31/(h+4.4))*rad)/60);}
export function apparentAltitude(geometric){let lo=geometric,hi=geometric+1.1;for(let i=0;i<32;i++){const mid=(lo+hi)/2;if(mid-refractionDegrees(mid)<geometric)lo=mid;else hi=mid;}return (lo+hi)/2;}
export function apparentSunDirection(direction){const elevation=apparentAltitude(Math.asin(direction[1])/rad)*rad,h=Math.hypot(direction[0],direction[2]);return [direction[0]/Math.max(h,1e-9)*Math.cos(elevation),Math.sin(elevation),direction[2]/Math.max(h,1e-9)*Math.cos(elevation)];}
export const solarRefractionGLSL=`float solarRefraction(float elevation){float h=clamp(degrees(elevation),-.5,89.9);return radians(max(0.,1./tan(radians(h+7.31/(h+4.4)))/60.));}
vec3 unrefractSunRay(vec3 d){float apparent=asin(clamp(d.y,-1.,1.));float h=apparent-solarRefraction(apparent);return vec3(normalize(d.xz+vec2(1e-9)).x*cos(h),sin(h),normalize(d.xz+vec2(1e-9)).y*cos(h));}`;
