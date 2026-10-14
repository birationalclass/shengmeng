import {SCREEN_FONT,SCREEN_COLORS} from './smart-screen-style.js?v=unframed-controls-1';
// A small on-glass library. Building this menu never fetches lesson/audio assets.
export function createHallProgramScreen(T,scene,{reports,x=16.35}){
 const group=new T.Group();group.name='Hall classroom and report library';scene.add(group);
 const targets=[],items=[];let tab='reports',language='en',active=null,pending=null,stored=false;
 const isCourse=r=>r?.kind==='classroom';
 function item(action,y,{left=x,width=4.6,height=.68}={}){
  const canvas=document.createElement('canvas');canvas.width=1024;canvas.height=Math.round(1024*height/width);const texture=new T.CanvasTexture(canvas);texture.colorSpace=T.SRGBColorSpace;
  const mesh=new T.Mesh(new T.PlaneGeometry(width,height),new T.MeshBasicMaterial({map:texture,transparent:true,depthWrite:false,toneMapped:false}));mesh.position.set(left,y,-11.324);mesh.name='Hall library '+action;mesh.userData={action,smartGlass:true,canvas,texture};group.add(mesh);targets.push(mesh);items.push(mesh);return mesh;
 }
 const classroom=item('program:classroom',4.52,{left:x-1.16,width:2.24,height:.51}),reportTab=item('program:reports',4.52,{left:x+1.16,width:2.24,height:.51});
 const reportRows=reports.filter(r=>!isCourse(r)).map((report,i)=>({report,mesh:item('report:'+report.id,3.30-i*.76)}));
 const courseRows=[item('program:course',3.30,{height:.76}),item('course:catalog',2.50),item('course:period:1',1.68),item('course:period:2',.92),item('course:manuscript',.16)];
 function label(mesh,title,subtitle='',selected=false,icon=null){const canvas=mesh.userData.canvas,c=canvas.getContext('2d');c.clearRect(0,0,canvas.width,canvas.height);c.save();c.translate(0,(canvas.height-200)/2);c.textAlign='right';c.textBaseline='middle';c.fillStyle=selected?SCREEN_COLORS.active:SCREEN_COLORS.text;c.strokeStyle=c.fillStyle;c.lineWidth=4;c.lineCap='square';
  if(icon){c.save();c.translate(100,30);if(icon==='classroom'){c.strokeRect(0,0,112,78);c.beginPath();c.moveTo(25,110);c.lineTo(85,110);c.moveTo(56,78);c.lineTo(56,110);c.moveTo(22,26);c.lineTo(90,26);c.moveTo(22,50);c.lineTo(67,50);c.stroke();}else{c.beginPath();c.moveTo(0,10);c.quadraticCurveTo(25,-5,56,10);c.quadraticCurveTo(85,-5,112,10);c.lineTo(112,100);c.quadraticCurveTo(85,85,56,100);c.quadraticCurveTo(25,85,0,100);c.closePath();c.moveTo(56,10);c.lineTo(56,100);c.stroke();}c.restore();}
  const font=SCREEN_FONT;c.font='500 '+(icon?104:63)+'px '+font;c.fillText(title,990,subtitle?65:98);if(subtitle){c.font='400 35px '+font;c.fillStyle=SCREEN_COLORS.muted;c.fillText(subtitle,990,141);}if(selected){c.fillStyle=SCREEN_COLORS.active;c.fillRect(icon?260:750,185,icon?730:240,2);}c.restore();mesh.userData.visibleLabel=title+(subtitle?' · '+subtitle:'');mesh.userData.fontFamily=font;mesh.userData.selected=selected;mesh.userData.texture.needsUpdate=true;
 }
 function paint(){const zh=language==='zh';label(classroom,zh?'课堂':'Classroom','',tab==='classroom','classroom');label(reportTab,zh?'报告':'Reports','',tab==='reports','reports');
  for(const {report,mesh}of reportRows){mesh.visible=tab==='reports';const chosen=(!stored&&active?.id===report.id)||pending?.id===report.id;label(mesh,report.label||(zh?report.speaker:report.speakerEn),pending?.id===report.id?(zh?'正在准备…':'Preparing…'):(zh?report.topic:report.topicEn),chosen);}
  courseRows.forEach(m=>m.visible=tab==='classroom');const selected=isCourse(active);label(courseRows[0],zh?'代数学 I':'Algebra I',zh?'2026 秋 · §2.6 西罗定理与应用':'Autumn 2026 · §2.6 Sylow theorems',selected);label(courseRows[1],zh?'课程目录':'Course schedule',zh?'26 次课 · 查看 GitHub 课程信息':'26 meetings · public course information');label(courseRows[2],zh?'第一课时':'Lesson 1',zh?'45 分钟 · 定理、计数与正规性':'45 min · theorems, counting, normality');label(courseRows[3],zh?'第二课时':'Lesson 2',zh?'45 分钟 · 小阶群与群作用':'45 min · small groups and actions');label(courseRows[4],zh?'讲稿与课堂任务':'Manuscript and activities',zh?'两课时逐行讲稿 · 中间休息 5 分钟':'Line-by-line notes · 5-minute break');
 }
 paint();return{group,targets,get tab(){return tab;},setState(report,waiting,lang,isStored){active=report;pending=waiting;language=lang;stored=isStored;paint();},select(report){active=report;tab=isCourse(report)?'classroom':'reports';paint();},action(action){if(action==='program:classroom'||action==='program:course')tab='classroom';else if(action==='program:reports')tab='reports';else return false;paint();return true;},dispose(){for(const m of items){m.geometry.dispose();m.material.dispose();m.userData.texture.dispose();}scene.remove(group);}};
}
