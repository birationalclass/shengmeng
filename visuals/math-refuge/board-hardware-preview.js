// Submit compile/render work for the unfolded hardware, then restore the real
// stored scene immediately. Do not advance clocks, playback, lids or controls.
export function withBoardHardwarePreview(root,rig,work){
 const visibility=[],position=rig?.position.clone();
 root.traverse(object=>{visibility.push([object,object.visible]);object.visible=true;});
 if(rig)rig.position.y=0;
 root.updateMatrixWorld(true);
 try{return work();}
 finally{
  for(const [object,visible] of visibility)object.visible=visible;
  if(rig)rig.position.copy(position);
  root.updateMatrixWorld(true);
 }
}
