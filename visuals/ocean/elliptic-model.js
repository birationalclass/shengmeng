// World units are metres. The defining equation uses kilometre coordinates.
export const FIELD={minX:-4096,minZ:-8192,size:16384};
export const HALF_WIDTH=50;
export function ringPoint(t){const x=(1-Math.cos(t))/2;return [x*1000,-500*Math.sin(t)*Math.sqrt(2-x)];}
export function branchPoint(t){const x=2+t*t;return [1000*x,-1000*t*Math.sqrt(x*(x-1))];}
function smooth(a,b,x){const t=Math.max(0,Math.min(1,(x-a)/(b-a)));return t*t*(3-2*t);}
// Right branch settles continuously into the common -18 m seabed.
export function coastalDrop(x,z){const descent=smooth(1800,7300,Math.abs(z));return 24*smooth(1200,1600,x)*descent*descent;}
// Broad, stationary relief: at most 10 cm, fading into the submerged skirts.
export function sandRelief(distance,x,z){return (.07*Math.sin(x*.022+z*.015)+.03*Math.sin(x*.043-z*.027))*(1-smooth(40,140,Math.abs(distance)));}
export function bedHeight(distance,x=0,z=0){return Math.max(-18,.055*(HALF_WIDTH-Math.sqrt(distance*distance+4))+sandRelief(distance,x,z)-coastalDrop(x,z));}

export function tideLevel(state){return state.tide+(state.tidal ? .28*Math.sin(state.time*Math.PI/20) : 0);}

export const terrainGLSL=`
uniform sampler2D uDistance;
uniform vec2 uOrigin;
uniform float uGrid,uTide;
float curveDistance(vec2 p){
 vec2 uv=(p-vec2(${FIELD.minX.toFixed(1)},${FIELD.minZ.toFixed(1)}))/${FIELD.size.toFixed(1)};
 if(any(lessThan(uv,vec2(0.)))||any(greaterThan(uv,vec2(1.))))return 400.;
 vec2 packed=texture2D(uDistance,uv).rg;
 return dot(packed,vec2(652.8,2.55));
}
float coastalDrop(vec2 p){float descent=smoothstep(1800.,7300.,abs(p.y));return 24.*smoothstep(1200.,1600.,p.x)*descent*descent;}
float sandRelief(float d,vec2 p){return (.07*sin(p.x*.022+p.y*.015)+.03*sin(p.x*.043-p.y*.027))*(1.-smoothstep(40.,140.,abs(d)));}
float beachHeight(vec2 p){float d=curveDistance(p);return max(-18.,.055*(50.-sqrt(d*d+4.))+sandRelief(d,p)-coastalDrop(p));}
vec3 bedNormal(vec2 p){return normalize(vec3(beachHeight(p-vec2(.5,0.))-beachHeight(p+vec2(.5,0.)),1.,beachHeight(p-vec2(0.,.5))-beachHeight(p+vec2(0.,.5))));}
#ifdef COAST_FRAGMENT
vec3 gridColor(vec3 col,vec2 p){
 vec2 q=p/250.;vec2 fw=max(fwidth(q),vec2(.00001));
 vec2 g=abs(fract(q-.5)-.5)/fw;
 float line=1.-smoothstep(.4,1.1,min(g.x,g.y));
 return mix(col,vec3(.64,.82,.79),line*.36*uGrid);
}
#endif
`;

// Same spectral source as 02; geometry resolves long waves and the shared
// optical material resolves the filtered capillary bands at pixel scale.
export const waveGLSL=`
uniform vec4 uWaves[32];uniform vec2 uPhases[32];
float waterLevel(vec2 p){
 float depth=max(0.,uTide-beachHeight(p));float h=0.;
 for(int i=0;i<16;i++){
  vec4 w=uWaves[i];float phase=dot(p,w.xy)*w.z-uTime*uPhases[i].x+uPhases[i].y;
  float resolved=1.-smoothstep(180./w.z,500./w.z,length(p-cameraPosition.xz));
  h+=w.w*sin(phase)*resolved;
 }
 float shore=(uTide-beachHeight(p))/.055;
 float approach=sin(shore*.48-uTime*1.5+noise(p*.016)*2.);
 float shoal=exp(-pow((depth-.6)/.85,2.));
 h=h*uWave*1.7*smoothstep(0.,2.5,depth)+approach*uWave*.11*shoal;
 return uTide+h;
}
`;
