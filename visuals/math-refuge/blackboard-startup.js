const frame=()=>new Promise(resolve=>requestAnimationFrame(resolve));
const array=value=>value.toArray?.()||value;
// The loading cover stays visible until the exact entry path is ready. Nothing
// here starts speech, reveals future ink or advances a physical board.
export async function prepareBlackboardEntry({lecture,renderer,scene,camera,target,prepareTextures=async()=>{},onStage=()=>{},turn=frame,now=()=>performance.now()}){
 const stages=[],started=now();
 async function measure(stage,label,work){onStage(stage,label);const start=now(),result=await work();stages.push({stage,ms:now()-start});await turn();return result;}
 await measure('textures','准备报告厅与黑板贴图',prepareTextures);
 await measure('lookahead','准备首板及下一板内容与语音',()=>lecture.prepareEntryBoards(2));
 await measure('surfaces','分配六块黑板的书写纹理',()=>lecture.prepareHardwareSurfaces());
 const probe=camera.clone(),view=lecture.cameraView(camera.aspect,57),overview={position:array(camera.position),target:array(target),fov:camera.fov},focused={position:array(view.position),target:array(view.target),fov:view.fov};
 const poses=[overview,{position:overview.position.map((v,i)=>(v+focused.position[i])/2),target:overview.target.map((v,i)=>(v+focused.target[i])/2),fov:(overview.fov+focused.fov)/2},focused];
 await measure('gpu','预热进入镜头与黑板材质',async()=>{
  scene.updateMatrixWorld(true);
  await lecture.previewOpeningHardware(()=>renderer.compileAsync?renderer.compileAsync(scene,probe):renderer.compile(scene,probe));
  for(const pose of poses){probe.position.fromArray(pose.position);probe.lookAt(...pose.target);probe.fov=pose.fov;probe.updateProjectionMatrix();probe.updateMatrixWorld();scene.updateMatrixWorld(true);lecture.previewOpeningHardware(()=>renderer.render(scene,probe));await turn();}
  // Restore the actual overview buffer before uncovering the canvas: a warm
  // focused view must never flash once before the real camera starts moving.
  scene.updateMatrixWorld(true);renderer.render(scene,camera);
  renderer.getContext?.().finish?.();
 });
 const result={ready:true,totalMs:now()-started,stages,programs:renderer.info.programs?.length||0,firstBoards:2,wholeCourseRequired:false};onStage('ready','进入课堂');return result;
}
