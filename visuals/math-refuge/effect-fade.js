// Frame-rate-independent fades; zero elapsed time never snaps a newly loaded effect.
export function fadeToward(value,target,dt,seconds=1.2){
 const step=Math.max(0,Math.min(.1,Number(dt)||0));
 return value+(target-value)*(-Math.expm1(-step/seconds));
}
