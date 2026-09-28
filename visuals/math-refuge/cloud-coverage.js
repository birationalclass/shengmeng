// Cloud cover is calibrated on the eligible horizontal cloud-layer area only.
const smooth=(a,b,x)=>{const t=Math.max(0,Math.min(1,(x-a)/(b-a)));return t*t*(3-2*t);};
const fract=x=>x-Math.floor(x);
function hash(x,y){let a=fract(x*.1031),b=fract(y*.1031),c=a;const d=a*(b+33.33)+b*(c+33.33)+c*(a+33.33);a+=d;b+=d;c+=d;return fract((a+b)*c);}
function noise(x,y){const a=Math.floor(x),b=Math.floor(y),u=smooth(0,1,x-a),v=smooth(0,1,y-b);return (hash(a,b)*(1-u)+hash(a+1,b)*u)*(1-v)+(hash(a,b+1)*(1-u)+hash(a+1,b+1)*u)*v;}
export function cloudRegion(x,z){const a=x+noise(x*.031,z*.031)*8,b=z+noise(x*.027+19,z*.027+19)*8;return .68*noise(a*.065,b*.065)+.32*noise(a*.151+37,b*.151+37);}
// No special regions: calibrate coverage over the entire cloud layer.
export function excludedCloudArea(){return 0;}
export function cloudCoverageArea(bearings,seed=[0,0]){
 const samples=[];let excluded=0,total=0;
 for(let i=0;i<4096;i++){const r=60*Math.sqrt((i+.5)/4096),a=i*2.399963229728653,x=r*Math.cos(a),z=r*Math.sin(a),cut=excludedCloudArea(x,z,bearings);total++;if(cut>0){excluded++;continue;}samples.push(cloudRegion(x-seed[0],z-seed[1]));}
 return {samples,total,excluded,eligible:samples.length};
}
export function coverageThreshold(area,coverage){
 if(coverage<=0)return 1.1;if(coverage>=1)return -.1;
 let lo=-.1,hi=1.1;for(let i=0;i<18;i++){const mid=(lo+hi)/2,cover=area.samples.reduce((n,v)=>n+smooth(mid-.035,mid+.035,v),0)/Math.max(1,area.eligible);if(cover>coverage)lo=mid;else hi=mid;}return (lo+hi)/2;
}

// Suppress distant occurrence, not opacity. Release gently near 80% coverage.
export function distantCloudCoverage(coverage){return coverage*(.5+.5*smooth(.78,.8,coverage));}
