// Hover sensors stay fixed while the leaves slide, avoiding open/close flicker.
export function createAutomaticDoors(T,glass,metal){
  const doors=[],targets=[],geometry=new T.BoxGeometry(1,1,1);
  const sensorMaterial=new T.MeshBasicMaterial({transparent:true,opacity:0,depthWrite:false,side:T.DoubleSide});
  function add(parent,{x,y,z,width,height,axis,name}){
    const group=new T.Group();group.name='Automatic seminar door '+name;
    group.position.set(x,y+height/2,z);if(axis==='z')group.rotation.y=Math.PI/2;parent.add(group);
    const leaves=[];
    for(const sign of [-1,1]){
      const leaf=new T.Group();leaf.position.x=sign*width/4;leaf.position.z=sign*.019;group.add(leaf);
      const pane=new T.Mesh(geometry,glass);pane.scale.set(width/2+.012,height,.026);leaf.add(pane);
      for(const edge of [-1,1]){
        const jamb=new T.Mesh(geometry,metal);jamb.scale.set(.013,height,.032);jamb.position.x=edge*width/4;leaf.add(jamb);
      }
      const handle=new T.Mesh(geometry,metal);handle.scale.set(.018,.38,.045);handle.position.set(-sign*(width/4-.10),-.10,.055);leaf.add(handle);
      leaves.push({leaf,sign});
    }
    const rail=new T.Mesh(geometry,metal);rail.scale.set(width*2.05,.075,.095);rail.position.y=height/2+.05;group.add(rail);
    const sensor=new T.Mesh(new T.PlaneGeometry(width*2.1,height+.15),sensorMaterial);sensor.name='Door hover sensor '+name;
    sensor.position.z=.08;sensor.userData={autoDoor:true,hovered:false,opening:0,axis,name};group.add(sensor);targets.push(sensor);
    const door={group,sensor,leaves,width,opening:0,closeDelay:0};doors.push(door);
    group.userData={side:name,automatic:true,leafCount:2,clearWidth:width};return group;
  }
  function update(dt,reduced=false){
    dt=Math.max(0,Math.min(.1,dt));
    for(const d of doors){
      d.closeDelay=d.sensor.userData.hovered?1.2:Math.max(0,d.closeDelay-dt);
      const target=d.closeDelay>0?1:0;
      d.opening=reduced?target:T.MathUtils.damp(d.opening,target,target?3.6:2.5,dt);
      for(const {leaf,sign} of d.leaves)leaf.position.x=sign*(d.width/4+d.opening*(d.width/2+.035));
      d.sensor.userData.opening=d.opening;
    }
  }
  return {add,update,targets,doors,dispose(){geometry.dispose();sensorMaterial.dispose();targets.forEach(t=>t.geometry.dispose());}};
}
