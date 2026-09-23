// Furniture dimensions are metres; the campus compensates its plan scale.
export function createLectern(T){
  const group=new T.Group();group.name='Modern interactive seminar lectern';
  const geometries=[],materials=[],targets=[];
  const material=(color,roughness,metalness=0)=>{const m=new T.MeshStandardMaterial({color,roughness,metalness,envMapIntensity:.22});materials.push(m);return m;};
  const graphite=material('#253234',.68,.55),bronze=material('#aa8c60',.52,.65),rubber=material('#151b1c',.94),meshMetal=material('#4b5557',.8,.4);
  function add(name,g,m,p,parent=group){geometries.push(g);const o=new T.Mesh(g,m);o.name=name;o.position.fromArray(p);o.castShadow=true;o.receiveShadow=true;o.userData.action='lectern:view';parent.add(o);targets.push(o);return o;}
  function rounded(name,w,h,d,r,m,p,parent=group){
    const s=new T.Shape(),x=-w/2,y=-h/2;
    s.moveTo(x+r,y);s.lineTo(x+w-r,y);s.quadraticCurveTo(x+w,y,x+w,y+r);s.lineTo(x+w,y+h-r);s.quadraticCurveTo(x+w,y+h,x+w-r,y+h);s.lineTo(x+r,y+h);s.quadraticCurveTo(x,y+h,x,y+h-r);s.lineTo(x,y+r);s.quadraticCurveTo(x,y,x+r,y);
    const g=new T.ExtrudeGeometry(s,{depth:d,bevelEnabled:false,curveSegments:8});g.translate(0,0,-d/2);return add(name,g,m,p,parent);
  }
  const base=rounded('Weighted rounded plinth',1,.67,.045,.12,graphite,[0,.038,0]);base.rotation.x=-Math.PI/2;
  rounded('Tapered graphite spine',.42,.85,.19,.08,graphite,[0,.49,-.07]).rotation.x=-.10;
  rounded('Console support collar',.29,.16,.17,.025,graphite,[0,.955,-.10]);
  rounded('Recessed bronze front panel',.29,.63,.008,.055,bronze,[0,.50,-.207]);
  for(let i=0;i<9;i++)add('Passive cooling vent',new T.BoxGeometry(.13,.007,.004),rubber,[0,.24+i*.019,-.215]);
  const console=new T.Group();console.name='Inclined touch console';console.position.set(0,1.035,0);console.rotation.x=-Math.PI/2+.22;group.add(console);
  rounded('Thin bronze console edge',1.16,.70,.065,.075,bronze,[0,0,0],console);
  rounded('Anti-glare graphite desktop',1.14,.68,.032,.065,graphite,[0,0,.041],console);
  const canvas=document.createElement('canvas');canvas.width=1024;canvas.height=512;
  const ctx=canvas.getContext('2d'),texture=new T.CanvasTexture(canvas);texture.colorSpace=T.SRGBColorSpace;
  const screenMat=new T.MeshBasicMaterial({map:texture,toneMapped:false});materials.push(screenMat);
  add('Embedded anti-glare touch display',new T.PlaneGeometry(.77,.385),screenMat,[0,0,.061],console);
  const pads=[];
  for(const [i,action] of ['lectern:previous','lectern:play','lectern:next'].entries()){
    const pad=add('Touch control '+action,new T.PlaneGeometry(.225,.095),new T.MeshBasicMaterial({transparent:true,opacity:0,depthWrite:false}),[(i-1)*.25,-.114,.063],console);
    materials.push(pad.material);pad.userData.action=action;pads.push(pad);
  }
  const progress=add('Touch board progress',new T.PlaneGeometry(.705,.067),new T.MeshBasicMaterial({transparent:true,opacity:0,depthWrite:false}),[0,-.027,.064],console);materials.push(progress.material);progress.userData={action:'page:seek:0',progress:true};
  for(const x of [.445,.494])rounded('USB-C recessed port',.025,.010,.003,.004,rubber,[x,-.12,.061],console);
  rounded('Stylus recess',.035,.30,.003,.016,rubber,[-.49,0,.061],console);
  rounded('Presentation stylus',.011,.24,.009,.005,bronze,[-.49,0,.067],console);
  add('Microphone weighted socket',new T.CylinderGeometry(.045,.05,.025,24),graphite,[-.45,1.09,-.21]);
  const path=new T.CatmullRomCurve3([new T.Vector3(-.45,1.10,-.21),new T.Vector3(-.45,1.34,-.20),new T.Vector3(-.39,1.49,-.04),new T.Vector3(-.30,1.47,.12)]);
  add('Flexible gooseneck microphone',new T.TubeGeometry(path,24,.009,8,false),graphite,[0,0,0]);
  const head=new T.Group();head.position.copy(path.getPoint(1));head.quaternion.setFromUnitVectors(new T.Vector3(0,1,0),path.getTangent(1));group.add(head);
  add('Microphone capsule',new T.CylinderGeometry(.022,.018,.078,16),rubber,[0,.025,0],head);
  for(let i=0;i<7;i++)add('Microphone grille ring',new T.TorusGeometry(.023,.0016,4,16),meshMetal,[0,.010+i*.008,0],head).rotation.x=Math.PI/2;
  for(let i=0;i<8;i++){const a=i*Math.PI/4;add('Microphone grille rib',new T.CylinderGeometry(.0012,.0012,.056,5),meshMetal,[Math.cos(a)*.023,.034,Math.sin(a)*.023],head);}
  group.userData={heightAboveFloor:1.49,desktopHeight:1.035,eyeHeight:1.68,action:'lectern:view'};
  let last='';
  function update({playing=false,page=0,total=0,seeking=false}={}){
    const key=[playing,page,total,seeking,pads.map(p=>p.userData.hovered?1:0).join('')].join(':');if(last===key)return;last=key;
    ctx.fillStyle='#122426';ctx.fillRect(0,0,1024,512);ctx.fillStyle='#9fcfc2';ctx.font='24px sans-serif';ctx.fillText('SEMINAR / SPEAKER CONSOLE',42,55);
    ctx.fillStyle='#e1e9e5';ctx.font='38px sans-serif';ctx.fillText('板书控制  /  CHALKBOARD',42,129);
    ctx.font='46px sans-serif';ctx.fillStyle='#efdfbf';ctx.fillText(`${page+1} / ${total}`,42,209);ctx.font='22px sans-serif';ctx.fillStyle='#a5b7b1';ctx.fillText(seeking?'正在定位…':playing?'WRITING':'PAUSED',735,209);
    ctx.fillStyle='#48665e';ctx.fillRect(44,287,936,6);ctx.fillStyle='#edc98e';const fraction=total>1?page/(total-1):0;ctx.fillRect(44,287,936*fraction,6);ctx.beginPath();ctx.arc(44+936*fraction,290,10,0,Math.PI*2);ctx.fill();
    for(const [i,label] of ['上一页',playing?'暂停板书':'继续板书','下一页'].entries()){
      ctx.fillStyle=pads[i].userData.hovered?'#416960':'#26413f';ctx.fillRect(30+i*332,344,298,123);
      ctx.fillStyle='#e5efea';ctx.font='30px sans-serif';ctx.fillText(label,72+i*332,417);
    }
    texture.needsUpdate=true;
  }
  update();
  return {group,targets,update,
    speakerPose(aspect=16/9){
      group.updateWorldMatrix(true,true);
      const position=group.localToWorld(new T.Vector3(0,1.68,1.35));
      const target=group.localToWorld(new T.Vector3(0,.80,-.55));
      const forward=target.clone().sub(position).normalize(),right=new T.Vector3().crossVectors(forward,new T.Vector3(0,1,0)).normalize(),up=new T.Vector3().crossVectors(right,forward);
      const display=group.getObjectByName('Embedded anti-glare touch display');
      let tangent=Math.tan(62*Math.PI/360);
      // Fit every screen corner with a 16% margin, including tall phones.
      for(const x of [-.385,.385])for(const y of [-.1925,.1925]){
        const v=display.localToWorld(new T.Vector3(x,y,0)).sub(position),depth=v.dot(forward);
        tangent=Math.max(tangent,Math.abs(v.dot(right))/(depth*Math.max(.25,aspect)*.84),Math.abs(v.dot(up))/(depth*.84));
      }
      return {position,target,fov:2*Math.atan(tangent)*180/Math.PI};
    },
    dispose(){texture.dispose();geometries.forEach(g=>g.dispose());materials.forEach(m=>m.dispose());}
  };
}
