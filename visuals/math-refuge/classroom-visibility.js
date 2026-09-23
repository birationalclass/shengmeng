// Conservative visibility gate: nearby, in view, and not behind another floor.
// Keep a distance hysteresis so hovering at a threshold cannot churn resources.
export function classroomVisible({distance,inFrustum,eyeY,floorY,height,insideRoom,room,wasVisible=false}){
  if(distance>(wasVisible?28:24)||!inFrustum)return false;
  if(insideRoom>=0&&insideRoom!==room)return false;
  if(insideRoom===room)return true;
  // Outside, opaque slabs occlude the classrooms on the other storeys.
  return eyeY>=floorY-.4&&eyeY<=floorY+height+.4;
}
