// Height is measured above the current tide, not world zero.
export function foamVisibility(height){
 const t=Math.max(0,Math.min(1,(height-25)/55));
 return 1-t*t*(3-2*t);
}
// Broad breaking-wave bands remain visible well above the fine spray cutoff.
export function breakerVisibility(height){
 const t=Math.max(0,Math.min(1,(height-180)/470));
 return 1-t*t*(3-2*t);
}
export function breakerDetailEnabled(height,previous=true){
 return previous ? height<680 : height<=650;
}
