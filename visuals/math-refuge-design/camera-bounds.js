// Applied after every camera source (orbit, dolly, pan, keys and tour).
// Keep both the eye and orbit target above the highest navigable water plane.
export function constrainAboveWater(camera,target,waterY){
  const floor=waterY+Math.max(1,Number(camera.near||0)*4);
  let changed=false;
  if(camera.position.y<floor){camera.position.y=floor;changed=true;}
  if(target.y<waterY+.05){target.y=waterY+.05;changed=true;}
  if(changed)camera.lookAt?.(target);
  return changed;
}
