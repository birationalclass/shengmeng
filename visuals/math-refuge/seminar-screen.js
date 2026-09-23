// Physical, frameless chapter → section controls on the glass left of the boards.
// Pass THREE in so the screen can also be checked without a browser renderer.
export function createSeminarScreen(T,scene,navigation){
  const group=new T.Group();group.name='Interactive seminar chapter and section glass';scene.add(group);
  const rows=[],targets=[];let chapter=null,selected='',language='zh';
  for(let i=0;i<10;i++){
    const canvas=document.createElement('canvas');canvas.width=1024;canvas.height=160;
    const texture=new T.CanvasTexture(canvas);texture.colorSpace=T.SRGBColorSpace;
    const mesh=new T.Mesh(new T.PlaneGeometry(4.8,.54),new T.MeshBasicMaterial({map:texture,transparent:true,depthWrite:false,toneMapped:false}));
    mesh.position.set(16.35,4.45-i*.52,-11.326);mesh.name='Seminar glass row '+i;
    mesh.userData={smartGlass:true,canvas,texture};group.add(mesh);rows.push(mesh);targets.push(mesh);
  }
  function paint(){
    const en=language==='en',parts=navigation.sections.filter(s=>s.chapter===chapter);
    const entries=chapter===null?
      [{text:en?'Kollár–Mori · choose a chapter':'Kollár–Mori · 选择章节'},...navigation.chapters.map(c=>({text:c.id+'  '+(en?c.en:c.title),action:'seminar:chapter:'+c.id})),{text:en?'One section per student session':'每次一位同学 · 讲一节'}]:
      [{text:en?'‹ Chapters':'‹ 返回章节',action:'seminar:chapters'},...parts.map(s=>({text:(s.id===selected?'▸ ':'')+'§ '+s.id+'  '+(en?s.en:s.title),action:'seminar:section:'+s.id,selected:s.id===selected})),{text:en?'Choose a section to begin':'选择小节后开始 · 节末停止'}];
    rows.forEach((mesh,i)=>{
      const entry=entries[i];mesh.visible=Boolean(entry);mesh.userData.action=entry?.action||null;
      if(!entry)return;
      const c=mesh.userData.canvas.getContext('2d');c.clearRect(0,0,1024,160);
      c.textAlign='right';c.textBaseline='middle';c.fillStyle=entry.selected?'#ffe2a6':entry.action?'#f4ead5':'#b7d3cc';
      let size=entry.action?57:42;const font=en?'Baskerville, Georgia, serif':'RefugeChinese, Kaiti SC, serif';
      c.font=size+'px '+font;while(c.measureText(entry.text).width>990&&size>28)c.font=(--size)+'px '+font;
      c.fillText(entry.text,1006,80);mesh.userData.texture.needsUpdate=true;mesh.userData.visibleLabel=entry.text;
    });
  }
  paint();
  return {group,targets,
    action(action){if(action==='seminar:chapters')chapter=null;else if(action.startsWith('seminar:chapter:'))chapter=Number(action.split(':')[2]);else return false;paint();return true;},
    select(id){selected=id;chapter=navigation.sections.find(s=>s.id===id)?.chapter??null;paint();},
    setLanguage(value){language=value;paint();},
    dispose(){rows.forEach(m=>{m.geometry.dispose();m.material.dispose();m.userData.texture.dispose();});scene.remove(group);}
  };
}
