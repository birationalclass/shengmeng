// Hover sensors stay fixed while the leaves slide, avoiding open/close flicker.
export function createAutomaticDoors(T,glass,metal){
  const doors=[],targets=[],geometry=new T.BoxGeometry(1,1,1);
  const sensorMaterial=new T.MeshBasicMaterial({transparent:true,opacity:0,depthWrite:false,side:T.DoubleSide});
  function add(parent,{x,y,z,width,height,axis,name,frameMaterial=metal}){
    const group=new T.Group();group.name='Automatic seminar door '+name;
    group.position.set(x,y+height/2,z);if(axis==='z')group.rotation.y=Math.PI/2;parent.add(group);
    const leaves=[],seams=[];
    const seamMaterial=name==='west'?frameMaterial.clone():null;
    if(seamMaterial){seamMaterial.transparent=true;seamMaterial.opacity=0;seamMaterial.depthWrite=false;}
    for(const sign of [-1,1]){
      const leaf=new T.Group();leaf.position.x=sign*width/4;leaf.position.z=sign*.019;group.add(leaf);
      const pane=new T.Mesh(geometry,glass);pane.name='Full-height sliding glass leaf';pane.scale.set(width/2+.012,height,.026);leaf.add(pane);
      for(const edge of [-1,1]){
        const jamb=new T.Mesh(geometry,seamMaterial||frameMaterial);jamb.name='Sliding door seam';if(seamMaterial){jamb.visible=false;seams.push(jamb);}jamb.scale.set(.007,height,.022);jamb.position.x=edge*width/4;leaf.add(jamb);
        const bevel=new T.Mesh(geometry,seamMaterial||frameMaterial);bevel.name='Sliding door angled highlight bevel';bevel.scale.set(.0025,height,.004);bevel.position.set(edge*width/4+.0035,0,.012);bevel.rotation.y=Math.PI/4;if(seamMaterial){bevel.visible=false;seams.push(bevel);}leaf.add(bevel);
      }
      leaves.push({leaf,sign});
    }
    const rail=new T.Mesh(geometry,frameMaterial);rail.name='Ceiling recessed door track';rail.scale.set(width*2.05,.038,.045);rail.position.y=height/2+.05;group.add(rail);
    const sensor=new T.Mesh(new T.PlaneGeometry(width*2.1,height+.15),sensorMaterial);sensor.name='Door hover sensor '+name;
    sensor.position.z=.08;sensor.userData={autoDoor:true,hovered:false,opening:0,axis,name};group.add(sensor);targets.push(sensor);
    const door={group,sensor,leaves,width,height,opening:0,closeDelay:0,seamMaterial,seams,seamOpacity:0};doors.push(door);
    group.userData={side:name,automatic:true,leafCount:2,clearWidth:width,clearHeight:height,transom:false};return group;
  }
  const a=new T.Vector3(),b=new T.Vector3(),direction=new T.Vector3(),hit=new T.Vector3();
  const zone=new T.Box3(),ray=new T.Ray();
  function cameraApproaches(d,path){
    if(!path?.length)return false;
    d.group.updateWorldMatrix(true,false);
    // Door-local sensing keeps other floors and neighbouring facades independent.
    zone.min.set(-d.width/2-.45,-d.height/2-.25,-3);
    zone.max.set(d.width/2+.45,d.height/2+.25,3);
    d.group.worldToLocal(a.copy(path[0]));
    if(zone.containsPoint(a))return true;
    for(let i=1;i<path.length;i++){
      d.group.worldToLocal(b.copy(path[i]));
      const length=direction.subVectors(b,a).length();
      if(length>1e-6){ray.set(a,direction.divideScalar(length));if(ray.intersectBox(zone,hit)&&hit.distanceTo(a)<=length)return true;}
      a.copy(b);
    }
    return false;
  }
  function update(dt,reduced=false,cameraPath=null){
    dt=Math.max(0,Math.min(.1,dt));
    for(const d of doors){
      d.closeDelay=(d.sensor.userData.hovered||cameraApproaches(d,cameraPath))?1.2:Math.max(0,d.closeDelay-dt);
      const target=d.closeDelay>0?1:0;
      d.opening=reduced?target:T.MathUtils.damp(d.opening,target,target?3.6:2.5,dt);
      if(!target&&d.opening<.001)d.opening=0;
      if(d.seamMaterial){
        const show=target||d.opening>0?1:0;
        d.seamOpacity=reduced?show:T.MathUtils.damp(d.seamOpacity,show,show?5:3,dt);
        if(!show&&d.seamOpacity<.005)d.seamOpacity=0;
        d.seamMaterial.opacity=d.seamOpacity;d.seams.forEach(s=>{s.visible=d.seamOpacity>0;});
      }
      for(const {leaf,sign} of d.leaves)leaf.position.x=sign*(d.width/4+d.opening*(d.width/2+.035));
      d.sensor.userData.opening=d.opening;
    }
  }
  return {add,update,targets,doors,dispose(){geometry.dispose();sensorMaterial.dispose();doors.forEach(d=>d.seamMaterial?.dispose());targets.forEach(t=>t.geometry.dispose());}};
}
