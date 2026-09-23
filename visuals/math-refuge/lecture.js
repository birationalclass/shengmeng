import {createSeminarScreen} from './seminar-screen.js?v53-section-sessions';
import * as THREE from 'three';
import {LectureClock,boardHeights,BOARD_LAYOUT} from './lecture-state.js?v53-section-sessions';
import {inkGuides,inkReveal,strokeReveal,writingPose,writingPlan,erasingPlan,eraserPose,wetOpacity,chalkLength,DRY_SECONDS,ERASER_HALF_WIDTH as EW,ERASER_HALF_HEIGHT as EH} from './chalk-motion.js?v49-late-frames';
import {paintChalkStroke} from './chalk-annotations.js?v51-local-definitions';

import {chalkCopy,composeChalkPage} from './chalk-language.js?v51-local-definitions';

import {REPORTS} from './report-catalog.js?v=34-duan-seminar';
import {createReportLoader} from './report-loader.js?v53-section-sessions';

import {createBoardHardware,TRAY,BOARD_MOUNT_OFFSET} from './board-hardware.js?v=43-tight-boards';
import {SCREEN_FONT,silverInk,seminarDate,addTextSheen,updateTextSheen} from './smart-screen.js?v=36-board-detail';

const W=1536,H=640,BOARD_W=BOARD_LAYOUT.width,BOARD_H=BOARD_LAYOUT.height;
const phaseNames={lift:'升降换板',erase:'擦除板书',write:'粉笔书写',hold:'停留阅读'};
export async function createLecture(scene,renderer,options={}){
  const reports=options.reports||REPORTS;
  let activeReport=reports.find(report=>report.id===(options.defaultReport||'hu'))||reports[0];
  const prepareReport=createReportLoader(),openingReport=await prepareReport(activeReport);
  let navigation=openingReport.navigation;
  let pages=openingReport.pages,clock=new LectureClock(pages.length),reportRequest=0,pendingReport=null,seekRequest=0,seeking=false;
  let seekPinned=new Set(),hasSelection=!options.requireSelection,renderActive=true,hydrating=false,renderEpoch=0;
  const estimateDurations=()=>pages.forEach((p,i)=>clock.setDurations(i,{write:p.kind?12:Math.max(23,18+(p.text?.length||0)*.24+(p.tex?.length||0)*.07),erase:24,hold:p.kind==='cover'?2:8}));
  estimateDurations();
  const cache=new Map(),pending=new Map(),guides=new Map(),erasePlans=new Map(),pageRows=new Map();let loadingError=null,version=0,language='zh',generation=0;
  if(document.fonts)await Promise.all([document.fonts.load('42px RefugeChinese'),document.fonts.load('42px RefugeLatin'),document.fonts.load('42px RefugeMath')]);
  function load(index,preparedImage){
    if(index<0)return Promise.resolve(null);
    if(cache.has(index))return Promise.resolve(cache.get(index));
    if(pending.has(index))return pending.get(index);
    const epoch=generation,lang=language;
    const job=new Promise((resolve,reject)=>{
      const image=preparedImage||new Image();const ready=()=>{
        if(epoch!==generation){resolve(null);return;}
        const sample=document.createElement('canvas');sample.width=W;sample.height=H;const sampleCtx=sample.getContext('2d',{willReadFrequently:true});
        const rows=composeChalkPage(sampleCtx,pages[index],index,lang,image,{deferStrokes:true});pageRows.set(index,rows);
        cache.set(index,sample);pending.delete(index);version++;
        let pixels=null;try{if(sampleCtx.getImageData)pixels=sampleCtx.getImageData(0,0,W,H);}catch{ /* Measured text bounds remain a safe fallback. */ }
        if(pixels)guides.set(index,inkGuides(pixels,rows));
        const wipe=erasingPlan(pixels,rows);erasePlans.set(index,wipe);
        clock.setDurations(index,{write:Math.max(.8,writingPlan(rows,guides.get(index)).duration),erase:Math.max(.4,wipe.duration),hold:pages[index].kind==='cover'?2:8});
        // Retain six on-board pages and the active/next page, evict other SVGs.
        const keep=new Set([...seekPinned,...clock.slots.map(s=>s.page),clock.page,Math.min(clock.page+1,pages.length-1)]);
        for(const key of cache.keys())if(cache.size>10&&!keep.has(key)){cache.delete(key);guides.delete(key);erasePlans.delete(key);pageRows.delete(key);}
        resolve(sample);
      };
      if(preparedImage){queueMicrotask(ready);return;}
      image.onload=ready;image.onerror=()=>{if(epoch!==generation){resolve(null);return;}pending.delete(index);reject(new Error('板书资源加载失败，请刷新重试。'));};image.src=pages[index].formulaAsset+'?v53-section-sessions';
    });pending.set(index,job);return job;
  }
  await load(0,openingReport.cover);
  if(navigation?.sections?.length)clock.stopAt=navigation.sections[0].end;
  const boards=[],mix=[0,0,0],targets=[0,0,0];let playing=hasSelection,accumulator=0,writingSpeed=1;
  const hardware=createBoardHardware(THREE),frameMaterial=hardware.wood;
  const metal=new THREE.MeshStandardMaterial({color:'#ad9d87',roughness:.84,metalness:.25,envMapIntensity:.25});
  const cube=new THREE.BoxGeometry(1,1,1);
  const trayChalkGeometry=new THREE.CylinderGeometry(.018,.015,.16,10);
  const trayChalkMaterials=['#f5efdc','#e9aa24','#e75575','#339bdd'].map(color=>new THREE.MeshStandardMaterial({color,roughness:1,emissive:color,emissiveIntensity:.18}));
  function part(parent,p,s,material){const mesh=new THREE.Mesh(cube,material);mesh.position.fromArray(p);mesh.scale.fromArray(s);parent.add(mesh);return mesh;}
  for(let pair=0;pair<3;pair++){
    const x=22.4+pair*5.6;
    const track=new THREE.Group();track.name='Double-channel lift track '+(pair+1);scene.add(track);
    track.position.z=BOARD_MOUNT_OFFSET;
    track.userData={column:pair,depths:[-10.505,-10.345].map(z=>z+BOARD_MOUNT_OFFSET),travel:[BOARD_LAYOUT.low,BOARD_LAYOUT.high],glassMounted:true};
    const railCenter=(BOARD_LAYOUT.railBottom+BOARD_LAYOUT.railTop)/2,railLength=BOARD_LAYOUT.railTop-BOARD_LAYOUT.railBottom+.06;
    for(const sign of [-1,1]){
      const railX=x+sign*2.745;
      for(const z of [-10.505,-10.345]){
        part(track,[railX+sign*.033,railCenter,z],[.028,railLength,.13],metal);
        for(const dz of [-.066,.066])part(track,[railX,railCenter,z+dz],[.075,railLength,.015],metal);
      }
      for(const y of [.62,railCenter,5.02]){
        part(track,[railX,y,-10.61],[.09,.075,.26],metal);
        part(track,[railX,y,-10.735],[.16,.17,.03],metal);
      }
    }
    for(const y of [BOARD_LAYOUT.railBottom,BOARD_LAYOUT.railTop]){const stop=part(track,[x,y,-10.51],[5.58,.06,.43],metal);stop.name=y===BOARD_LAYOUT.railTop?'Upper rail stop':'Lower rail stop';}
    for(let side=0;side<2;side++){
      const group=new THREE.Group();group.position.set(x,boardHeights(0)[side],-10.45+side*.16+BOARD_MOUNT_OFFSET);
      group.name=`Sliding chalkboard ${pair+1}${side?'B':'A'}`;scene.add(group);
      const canvas=document.createElement('canvas');canvas.width=W;canvas.height=H;
      const ctx=canvas.getContext('2d'),texture=new THREE.CanvasTexture(canvas);texture.colorSpace=THREE.SRGBColorSpace;
      texture.anisotropy=Math.min(16,renderer.capabilities.getMaxAnisotropy());texture.generateMipmaps=true;texture.minFilter=THREE.LinearMipmapLinearFilter;
      const roughCanvas=document.createElement('canvas');roughCanvas.width=W/4;roughCanvas.height=H/4;const roughCtx=roughCanvas.getContext('2d');roughCtx.fillStyle='white';roughCtx.fillRect(0,0,W/4,H/4);
      const roughTexture=new THREE.CanvasTexture(roughCanvas);
      // The backing is physically recessed by .01. Avoid slope-dependent
      // depth bias, which grows at grazing angles and can occlude the chalk.
      const surface=new THREE.Mesh(new THREE.PlaneGeometry(BOARD_W,BOARD_H),new THREE.MeshPhysicalMaterial({map:texture,color:'#c9c5bb',roughness:1,roughnessMap:roughTexture,metalness:0,specularIntensity:0,envMapIntensity:0,emissive:0x000000,emissiveIntensity:0,polygonOffset:true,polygonOffsetFactor:0,polygonOffsetUnits:-1}));
      surface.name='Matte writing face';group.add(surface);
      const body=part(group,[0,0,-.05],[BOARD_W,BOARD_H,.08],hardware.back);body.name='Solid opaque board body';
      for(const y of [-.65,.65]){const brace=part(group,[0,y,-.094],[BOARD_W-.16,.035,.022],frameMaterial);brace.name='Rear nanmu stiffener';}
      for(const y of [-BOARD_H/2,BOARD_H/2]){const edge=part(group,[0,y,-.026],[BOARD_W+.035,.035,.12],frameMaterial);edge.name='Thin nanmu frame';}
      for(const px of [-BOARD_W/2,BOARD_W/2]){const edge=part(group,[px,0,-.026],[BOARD_H,.035,.12],frameMaterial);edge.rotation.z=Math.PI/2;edge.name='Thin nanmu frame';}
      for(const sign of [-1,1])for(const y of [-.70,.70]){
        const carriage=part(group,[sign*2.702,y,-.055],[.145,.13,.055],metal);carriage.name='Rail carriage bracket';
        const wheel=new THREE.Mesh(new THREE.CylinderGeometry(.049,.049,.045,12),hardware.rubber);
        wheel.name='Guide roller';wheel.rotation.z=Math.PI/2;wheel.position.set(sign*2.745,y,-.055);group.add(wheel);
      }
      boards.push({group,canvas,ctx,texture,roughCtx,roughTexture,wet:null,last:''});
    }
    const tray=new THREE.Group();tray.name='Wide nanmu chalk tray '+(pair+1);tray.userData={column:pair,depth:TRAY.depth,centerZ:TRAY.z,floorTop:TRAY.top};scene.add(tray);
    part(tray,[x,TRAY.y,TRAY.z],[5.42,.06,TRAY.depth],frameMaterial);
    for(const z of [TRAY.z-TRAY.depth/2,TRAY.z+TRAY.depth/2])part(tray,[x,TRAY.lipY,z],[5.42,.074,.025],frameMaterial);
    for(const dx of [-2.71,2.71])part(tray,[x+dx,TRAY.lipY,TRAY.z],[.025,.074,TRAY.depth],frameMaterial);
    for(let j=0;j<4;j++){
      const stick=new THREE.Mesh(trayChalkGeometry,trayChalkMaterials[j]);stick.name=`Tray chalk ${pair+1} ${j+1}`;
      stick.rotation.z=Math.PI/2;stick.rotation.y=(j%2?1:-1)*.08;stick.position.set(x-.95+j*.24,TRAY.top+.020,TRAY.z);
      stick.userData={column:pair,colorIndex:j};scene.add(stick);
    }
  }
  // Three synchronized controls, centered exactly beneath their board columns.
  const consoleButtons=[],consoleTextures=[];
  const touchCanvas=document.createElement('canvas');touchCanvas.width=1024;touchCanvas.height=384;
  const touchTexture=new THREE.CanvasTexture(touchCanvas);touchTexture.colorSpace=THREE.SRGBColorSpace;consoleTextures.push(touchTexture);
  for(let column=0;column<3;column++){
    const button=new THREE.Mesh(new THREE.PlaneGeometry(2.2,.65),new THREE.MeshBasicMaterial({transparent:true,opacity:0,colorWrite:false,depthWrite:false,toneMapped:false}));
    button.name=`Smart glass language touch surface ${column+1}`;button.position.set(22.4+column*5.6,-.16,-11.34);
    button.userData={action:'language',column,pressed:false,restZ:-11.34,lastLabel:'',smartGlass:true,singleToggle:true,glassPanel:0,canvas:touchCanvas,texture:touchTexture};
    const label=new THREE.Mesh(new THREE.PlaneGeometry(2.16,.60),new THREE.MeshBasicMaterial({map:touchTexture,transparent:true,opacity:1,depthWrite:false,toneMapped:false}));
    label.position.z=.008;label.userData.screenLabel=true;button.add(label);addTextSheen(THREE,button,touchTexture,2.16,.60);scene.add(button);consoleButtons.push(button);
  }
  function setConsoleState(){
    if(consoleButtons.every(button=>button.userData.lastLabel===language))return;
    const targetLanguage=language==='zh'?'en':'zh',label=targetLanguage==='zh'?'中':'Eng';
    for(const button of consoleButtons){button.userData.lastLabel=language;button.userData.visibleLabel=label;button.userData.targetLanguage=targetLanguage;}
    const c=touchCanvas.getContext('2d');c.clearRect(0,0,1024,384);
    c.textAlign='center';c.shadowBlur=0;
    c.font=targetLanguage==='zh'?'400 184px '+SCREEN_FONT:'400 176px Baskerville, "Iowan Old Style", Georgia, serif';
    c.fillStyle='#f0e4ca';c.fillText(label,512,250);
    touchTexture.needsUpdate=true;
  }
  const reportButtons=[],reportTextures=[];
  // Move the report list slightly left, retaining its full-size hit targets.
  const reportX=16.35;let dateLabel='',dateCheck=0;
  function glassLabel(width,height,x,y,name){
    const canvas=document.createElement('canvas');canvas.width=1024;canvas.height=240;
    const texture=new THREE.CanvasTexture(canvas);texture.colorSpace=THREE.SRGBColorSpace;reportTextures.push(texture);
    const mesh=new THREE.Mesh(new THREE.PlaneGeometry(width,height),new THREE.MeshBasicMaterial({map:texture,transparent:true,depthWrite:false,toneMapped:false}));
    mesh.position.set(x,y,-11.332);mesh.name=name;scene.add(mesh);return {mesh,canvas,texture};
  }
  const reportHeader=glassLabel(4.6,.55,reportX,4.45,'Smart glass report heading');
  addTextSheen(THREE,reportHeader.mesh,reportHeader.texture,4.6,.55);
  for(const [index,report] of (navigation?.sections?[]:reports).entries()){
    const label=glassLabel(4.6,.9,reportX,3.55-index*1.05,`Smart glass report ${report.id}`);
    const button=new THREE.Mesh(new THREE.PlaneGeometry(4.7,1.02),new THREE.MeshBasicMaterial({transparent:true,opacity:0,colorWrite:false,depthWrite:false,toneMapped:false}));
    button.position.set(reportX,3.55-index*1.05,-11.34);button.name=`Report selection ${report.speaker}`;
    scene.remove(label.mesh);label.mesh.position.set(0,0,.008);label.mesh.userData.screenLabel=true;button.add(label.mesh);addTextSheen(THREE,button,label.texture,4.6,.9);scene.add(button);
    Object.assign(button.userData,{action:`report:${report.id}`,reportId:report.id,smartGlass:true,pressed:false,canvas:label.canvas,texture:label.texture});reportButtons.push(button);
  }
  function setReportState(){
    dateLabel=seminarDate();
    const header=reportHeader.canvas.getContext('2d');header.clearRect(0,0,1024,240);header.textAlign='right';header.fillStyle=silverInk(header);header.font='400 78px Baskerville, "Iowan Old Style", Georgia, serif';
    header.fillText(dateLabel,996,154);reportHeader.mesh.userData.date=dateLabel;reportHeader.texture.needsUpdate=true;
    for(const [index,button] of reportButtons.entries()){
      const report=reports[index],waiting=report.id===pendingReport?.id,selected=report.id===(pendingReport||activeReport).id,c=button.userData.canvas.getContext('2d');
      c.clearRect(0,0,1024,240);c.textAlign='right';c.shadowBlur=0;c.fillStyle=silverInk(c);
      const font=language==='zh'?SCREEN_FONT:'Baskerville, "Iowan Old Style", Georgia, serif';
      c.font='400 78px '+font;
      const name=language==='zh'?report.speaker:report.speakerEn;c.fillText(name,996,91);
      if(selected){const px=996-c.measureText(name).width-38;c.font='400 55px Georgia, serif';c.fillStyle='#e4cf9c';c.fillText('▸',px,88);}
      c.font='400 40px '+font;c.fillStyle=silverInk(c);
      const topic=waiting?(language==='zh'?'正在准备报告…':'Preparing report…'):(language==='zh'?report.topic:report.topicEn),words=language==='zh'?[...topic]:topic.split(/(?<= )/);let line='',y=159;
      for(const word of words){if(c.measureText(line+word).width>960){c.fillText(line,996,y);line=word;y+=47;}else line+=word;}c.fillText(line,996,y);
      button.userData.texture.needsUpdate=true;button.userData.selected=selected;button.userData.selectionPointer=selected;
    }
  }
  const seminarScreen=navigation?.sections?createSeminarScreen(THREE,scene,navigation):null;
  if(seminarScreen)reportHeader.mesh.visible=false;
  const touchButtons=[...consoleButtons,...reportButtons,...(seminarScreen?.targets||[])];
  setConsoleState();setReportState();
  const chalk=new THREE.Mesh(new THREE.CylinderGeometry(.017,.014,.17,8),new THREE.MeshStandardMaterial({color:'#f3edda',roughness:1,metalness:0,emissive:'#e3dcc8',emissiveIntensity:.32,envMapIntensity:.15}));
  const chalkAxis=new THREE.Vector3(.22,-.42,.88).normalize();chalk.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0),chalkAxis);chalk.name='Writing chalk';scene.add(chalk);
  const eraserWidth=EW*2/W*BOARD_W,eraserHeight=EH*2/H*BOARD_H;
  const eraser=new THREE.Mesh(hardware.roundedBox(eraserWidth,eraserHeight,.08),frameMaterial);eraser.name='Moving blackboard eraser';scene.add(eraser);
  const felt=new THREE.Mesh(hardware.roundedBox(eraserWidth*.98,eraserHeight*.98,.025,.012),hardware.felt);felt.name='Textured layered felt';felt.position.z=-.0525;eraser.add(felt);
  const grip=new THREE.Mesh(hardware.roundedBox(eraserWidth*.7,eraserHeight*.54,.018,.016),frameMaterial);grip.name='Rounded palm grip';grip.position.z=.045;eraser.add(grip);
  for(const sign of [-1,1]){const seam=part(eraser,[0,sign*eraserHeight*.33,.043],[eraserWidth*.76,.006,.004],hardware.rubber);seam.name='Recessed finger groove';}
  for(let i=0;i<3;i++){const fibre=part(eraser,[0,0,-.044-i*.007],[eraserWidth*.985,eraserHeight*.985,.003],hardware.felt);fibre.name='Felt laminate';}
  const parkedErasers=Array.from({length:3},(_,column)=>{
    const parked=eraser.clone();parked.name=`Tray eraser ${column+1}`;parked.position.set(23.25+column*5.6,TRAY.restY,TRAY.z);parked.rotation.set(-Math.PI/2,0,.035);
    parked.userData={column,resting:true};scene.add(parked);return parked;
  });
  eraser.visible=false;
  let eraserColumn=0,eraserReturn=null,eraserPickup=null;
  const eraserContact=new THREE.Object3D();
  const particleCount=64,particlePositions=new Float32Array(particleCount*3).fill(-10000),particles=Array.from({length:particleCount},()=>({life:0,vx:0,vy:0}));
  const dustGeometry=new THREE.BufferGeometry();dustGeometry.setAttribute('position',new THREE.BufferAttribute(particlePositions,3));
  const dot=new Uint8Array(16*16*4);for(let y=0;y<16;y++)for(let x=0;x<16;x++){const i=(y*16+x)*4,r=Math.hypot((x-7.5)/7.5,(y-7.5)/7.5);dot.set([255,255,255,Math.round(Math.max(0,1-r)*200)],i);}
  const dotMap=new THREE.DataTexture(dot,16,16);dotMap.needsUpdate=true;
  const dustMaterial=new THREE.PointsMaterial({color:'#ece6cf',size:.014,map:dotMap,transparent:true,opacity:.36,depthWrite:false});
  const fallingDust=new THREE.Points(dustGeometry,dustMaterial);fallingDust.name='Falling chalk powder';fallingDust.frustumCulled=false;scene.add(fallingDust);
  let effectTime=0,wear=0,previousTip=null,lastWritePage=-1,particleCursor=0,dustAccumulator=0;
  const grain=document.createElement('canvas');grain.width=W;grain.height=H;
  const g=grain.getContext('2d');g.fillStyle='#193d33';g.fillRect(0,0,W,H);
  let seed=831;const random=()=>{seed=(seed*1664525+1013904223)>>>0;return seed/4294967296;};
  for(let i=0;i<12000;i++){g.fillStyle=i%2?'#e7f0d808':'#041c1b18';g.fillRect(random()*W,random()*H,1+random()*2,1);}
  const dust=document.createElement('canvas');dust.width=W;dust.height=H;
  const d=dust.getContext('2d');d.fillStyle='#193d3328';
  for(let i=0;i<6000;i++)d.fillRect(random()*W,random()*H,.5+random(),.6);
  // Reuse one incremental wipe cache: do not replay hundreds of clipped
  // full-resolution grain copies on every mobile animation frame.
  const wipeCanvas=document.createElement('canvas');wipeCanvas.width=W;wipeCanvas.height=H;
  const wipeCtx=wipeCanvas.getContext('2d');let wipeSamples=0;
  function draw(index){
    const board=boards[index],slot=clock.slots[index],ctx=board.ctx;
    const erasing=index===clock.active&&clock.phase==='erase'&&clock.progress>0;
    const wet=board.wet,wetAge=wet?effectTime-wet.started:Infinity;
    const wetKey=wet&&wet.progress>0&&wetAge<wet.duration+DRY_SECONDS?(Math.floor(effectTime*12)+':'+wet.progress.toFixed(3)):'';
    const key=`${slot.page}:${slot.progress.toFixed(3)}:${erasing?clock.progress.toFixed(3):''}:${cache.has(slot.page)}:${wetKey}`;
    if(!renderActive||hydrating)return;
    if(board.last===key)return;board.last=key;
    ctx.drawImage(grain,0,0);const image=cache.get(slot.page);
    if(image){
      const rows=pageRows.get(slot.page)||pages[slot.page].rows;
      // Reveal each complete mathematical row left to right, preserving exact
      // SVG fractions/superscripts. The grain is deterministic, never flickering.
      rows.forEach(([x,y,w,h],row)=>{
        if(rows[row].strokePath){paintChalkStroke(ctx,strokeReveal(rows,slot.progress,row,guides.get(slot.page)),rows[row].chalkColor);return;}
        const width=inkReveal(rows,slot.progress,row,guides.get(slot.page));
        if(width>0){ctx.save();ctx.beginPath();ctx.rect(x,y,width,h);ctx.clip();ctx.drawImage(image,0,0);ctx.restore();}
      });
      ctx.drawImage(dust,0,0);
      if(erasing){
        const end=Math.floor(clock.progress*700);
        for(let i=wipeSamples;i<=end;i++){
          const p=eraserPose(i/700,W,H,wet.plan);if(!p.contact)continue;
          wipeCtx.save();wipeCtx.translate(p.x,p.y);wipeCtx.rotate(p.angle);wipeCtx.beginPath();wipeCtx.rect(-EW,-EH,EW*2,EH*2);wipeCtx.clip();wipeCtx.rotate(-p.angle);wipeCtx.translate(-p.x,-p.y);wipeCtx.drawImage(grain,0,0);wipeCtx.restore();
        }
        wipeSamples=end+1;ctx.drawImage(wipeCanvas,0,0);
      }
    }
    const r=board.roughCtx;r.fillStyle='white';r.fillRect(0,0,W/4,H/4);
    if(wetKey)for(let i=0;i<=Math.floor(wet.progress*420);i++){
      const p=eraserPose(i/420,W,H,wet.plan),age=effectTime-wet.started-i/420*wet.duration,opacity=wetOpacity(Math.max(0,age));if(!p.contact||opacity<=0)continue;
      for(const [target,scale] of [[ctx,1],[r,.25]]){target.save();target.translate(p.x*scale,p.y*scale);target.rotate(p.angle);target.fillStyle=scale===1?`rgba(4,24,22,${opacity*.32})`:`rgba(0,0,0,${opacity*.6})`;target.fillRect(-EW*scale,-EH*scale,EW*2*scale,EH*2*scale);target.restore();}
    }
    board.roughTexture.needsUpdate=true;
    board.texture.needsUpdate=true;
  }
  function positionTool(tool,x,y){
    const board=boards[clock.active].group;
    tool.position.set(board.position.x+(x/W-.5)*BOARD_W,board.position.y+(.5-y/H)*BOARD_H,board.position.z+.014);
  }
  function select(page){clock.select(page);targets[Math.floor(clock.active/2)]=clock.active%2;version++;load(clock.page).catch(error=>{loadingError=error;});}
  async function seek(page){
    const request=++seekRequest,epoch=generation;
    const target=Math.max(clock.startAt,Math.min(clock.stopAt,Math.trunc(page)||0));
    seeking=true;seekPinned=new Set(Array.from({length:target-Math.max(clock.startAt,target-5)+1},(_,i)=>Math.max(clock.startAt,target-5)+i));
    try{
      await Promise.all(Array.from({length:target-Math.max(clock.startAt,target-5)+1},(_,i)=>load(Math.max(clock.startAt,target-5)+i)));
      if(request!==seekRequest||epoch!==generation)return false;
      clock.seek(target);
      for(let pair=0;pair<3;pair++){
        const a=clock.slots[pair*2].page,b=clock.slots[pair*2+1].page;
        mix[pair]=targets[pair]=b>a?1:0;
        boardHeights(mix[pair]).forEach((height,side)=>boards[pair*2+side].group.position.y=height);
      }
      eraserReturn=null;eraserPickup=null;eraser.visible=false;eraser.userData.state='resting';
      parkedErasers.forEach(e=>e.visible=true);chalk.visible=false;previousTip=null;
      particles.forEach(p=>p.life=0);particlePositions.fill(-10000);dustGeometry.attributes.position.needsUpdate=true;
      boards.forEach(b=>{b.wet=null;b.last='';});wipeCanvas.width=W;wipeSamples=0;
      boards.forEach((_,i)=>draw(i));version++;
      return true;
    }catch(error){if(request===seekRequest)loadingError=error;throw error;}
    finally{if(request===seekRequest){seeking=false;seekPinned.clear();}}
  }
  function update(dt,reduced=false){
    if(!renderActive||hydrating){if(playing&&hasSelection&&!reduced&&!seeking&&!hydrating)clock.advance(dt,writingSpeed);return;}
    dt=Math.max(0,Math.min(.1,dt));for(const b of touchButtons){updateTextSheen(THREE,b,dt,reduced);}updateTextSheen(THREE,reportHeader.mesh,dt,reduced);
    dateCheck+=dt;if(dateCheck>=1){dateCheck=0;if(seminarDate()!==dateLabel)setReportState();}if(playing&&!reduced)effectTime+=dt;
    const oldPhase=clock.phase,oldActive=clock.active;
    const ready=cache.has(clock.page)&&(clock.slots[clock.active].page<0||cache.has(clock.slots[clock.active].page));
    if(!ready&&!loadingError){load(clock.page).catch(error=>{loadingError=error;});load(clock.slots[clock.active].page).catch(error=>{loadingError=error;});}
    // Ink removal only starts after the felt reaches the board from its tray.
    const collectingEraser=clock.phase==='erase'&&eraser.userData.state!=='erasing';
    if(playing&&hasSelection&&ready&&!seeking&&!loadingError&&!reduced&&!collectingEraser){
      const prior=clock.page;clock.update(dt*(clock.phase==='write'?writingSpeed:1));
      if(prior!==clock.page){targets[Math.floor(clock.active/2)]=clock.active%2;load(clock.page).catch(error=>{loadingError=error;});}
    }
    if(clock.phase==='erase'){
      if(oldPhase!=='erase'||oldActive!==clock.active||!boards[clock.active].wet){boards[clock.active].wet={started:effectTime,progress:0,duration:clock.duration,plan:erasePlans.get(clock.slots[clock.active].page)};wipeCanvas.width=W;wipeSamples=0;}
      boards[clock.active].wet.progress=clock.progress;
    }else if(oldPhase==='erase'&&boards[oldActive].wet)boards[oldActive].wet.progress=1;
    if(reduced)for(const board of boards)board.wet=null;
    for(let pair=0;pair<3;pair++){
      mix[pair]=reduced?targets[pair]:THREE.MathUtils.damp(mix[pair],targets[pair],3,dt);
      boardHeights(mix[pair]).forEach((height,side)=>boards[pair*2+side].group.position.y=height);
    }
    chalk.visible=playing&&!reduced&&ready&&clock.phase==='write';
    const erasing=!reduced&&ready&&clock.phase==='erase';
    if(['erasing','pickup'].includes(eraser.userData.state)&&(!erasing||eraserColumn!==Math.floor(clock.active/2))){
      eraserReturn={column:eraserColumn,elapsed:0,position:eraser.position.clone(),quaternion:eraser.quaternion.clone()};
      eraserPickup=null;
    }
    if(reduced){eraserReturn=null;eraserPickup=null;}
    if(erasing){
      const column=Math.floor(clock.active/2);
      const starting=!eraserPickup&&(eraser.userData.state!=='erasing'||eraserColumn!==column);
      if(starting){
        const rest=parkedErasers[column];
        eraserPickup={elapsed:0,position:rest.position.clone(),quaternion:rest.quaternion.clone()};
        eraser.position.copy(rest.position);eraser.quaternion.copy(rest.quaternion);
      }
      eraserColumn=column;eraserReturn=null;eraser.visible=true;
      if(eraserPickup){
        if(playing&&!starting)eraserPickup.elapsed+=dt;
        const t=Math.min(1,eraserPickup.elapsed/1.4),ease=t*t*(3-2*t);
        const p=eraserPose(0,W,H,boards[clock.active].wet?.plan);
        positionTool(eraserContact,p.x,p.y);eraserContact.position.z+=.052+p.lift;eraserContact.rotation.set(.03,0,-p.angle);
        eraser.position.lerpVectors(eraserPickup.position,eraserContact.position,ease);
        eraser.position.z+=Math.sin(Math.PI*t)*.22;
        eraser.quaternion.slerpQuaternions(eraserPickup.quaternion,eraserContact.quaternion,ease);
        eraser.userData.state='pickup';
        if(t===1){eraserPickup=null;eraser.userData.state='erasing';boards[clock.active].wet.started=effectTime;}
      }else eraser.userData.state='erasing';
    }else if(eraserReturn){
      if(playing)eraserReturn.elapsed+=dt;
      const t=Math.min(1,eraserReturn.elapsed/1.4),ease=t*t*(3-2*t),rest=parkedErasers[eraserReturn.column];
      eraser.position.lerpVectors(eraserReturn.position,rest.position,ease);
      eraser.position.z+=Math.sin(Math.PI*t)*.22;
      eraser.quaternion.slerpQuaternions(eraserReturn.quaternion,rest.quaternion,ease);
      eraser.visible=t<1;eraser.userData.state=t<1?'returning':'resting';if(t===1)eraserReturn=null;
    }else{eraser.visible=false;eraser.userData.state='resting';}
    parkedErasers.forEach((rest,column)=>{rest.visible=!(eraser.visible&&column===eraserColumn);});
    if(chalk.visible){
      if(lastWritePage!==clock.page){lastWritePage=clock.page;previousTip=null;if(chalkLength(wear)<.06)wear=0;}
      const pose=writingPose(pageRows.get(clock.page)||pages[clock.page].rows,clock.progress,guides.get(clock.page));positionTool(chalk,pose.x,pose.y);chalk.position.z+=pose.contact?0:.055+pose.lift;
      chalk.material.color.set(pageRows.get(clock.page)?.[pose.row]?.chalkColor||'#f3edda');
      const tip=chalk.position.clone();
      if(previousTip&&pose.contact)wear+=Math.min(.07,tip.distanceTo(previousTip))*.007;
      const length=chalkLength(wear),propScale=1/(scene.scale.y||1);chalk.scale.set(propScale,length/.17*propScale,propScale);chalk.position.addScaledVector(chalkAxis,length*propScale/2);chalk.userData.length=length;chalk.userData.contact=pose.contact;previousTip=tip;
      dustAccumulator+=dt;
      if(pose.contact&&dustAccumulator>.09){dustAccumulator=0;const i=particleCursor++%particleCount;particles[i]={life:1.1,vx:(random()-.5)*.025,vy:-.015};particlePositions.set([tip.x,tip.y,tip.z+.016],i*3);}
    }else previousTip=null;
    if(erasing&&!eraserPickup){const p=eraserPose(clock.progress,W,H,boards[clock.active].wet?.plan);positionTool(eraser,p.x,p.y);eraser.position.z+=.052+p.lift;eraser.rotation.set(.03,0,-p.angle);}
    fallingDust.visible=!reduced;
    if(playing&&!reduced)for(let i=0;i<particleCount;i++){
      const p=particles[i];if(p.life<=0)continue;p.life-=dt;p.vy-=dt*.11;
      particlePositions[i*3]+=p.vx*dt;particlePositions[i*3+1]+=p.vy*dt;
      if(p.life<=0)particlePositions[i*3+1]=-10000;
    }
    dustGeometry.attributes.position.needsUpdate=playing&&!reduced;
    accumulator+=dt;
    if(accumulator>=.05||version){boards.forEach((_,i)=>draw(i));accumulator=0;version=0;}
  }
  // Reduced-motion users get complete static pages and explicit page controls.
  function staticPage(){clock.startWrite();clock.slots[clock.active].progress=1;clock.phase='hold';clock.elapsed=0;clock.ended=clock.page===clock.stopAt;version++;}
  boards.forEach((_,i)=>draw(i));
  // Keep the hardware and last completed texture visible at every distance.
  // Only the board carriers and tools have changing local transforms.
  const movingNodes=new Set([scene,...boards.map(b=>b.group),chalk,eraser]);
  scene.traverse(object=>{if(!movingNodes.has(object)){object.updateMatrix();object.matrixAutoUpdate=false;}});
  return {
    update,seek,root:scene,get renderActive(){return renderActive&&!hydrating;},get hasSelection(){return hasSelection;},
    get progress(){return {page:clock.page-clock.startAt,total:clock.stopAt-clock.startAt+1};},
    screenAction:action=>seminarScreen?.action(action),
    async setRenderActive(value){
      if(value===renderActive)return;renderActive=value;const epoch=++renderEpoch;
      if(!value){hydrating=false;chalk.visible=false;eraser.visible=false;fallingDust.visible=false;parkedErasers.forEach(e=>e.visible=true);return;}
      hydrating=true;const resume={page:clock.page,phase:clock.phase,progress:clock.progress};
      try{
        const visible=[...new Set([...clock.slots.map(s=>s.page),hasSelection?clock.page:-1])].filter(i=>i>=0);
        for(const index of visible){await load(index);if(epoch!==renderEpoch)return;await new Promise(resolve=>typeof requestAnimationFrame==='function'?requestAnimationFrame(resolve):resolve());}
        if(epoch!==renderEpoch)return;
        if(clock.page===resume.page&&clock.phase===resume.phase)clock.elapsed=resume.progress*clock.duration;
        for(let pair=0;pair<3;pair++){const a=clock.slots[pair*2].page,b=clock.slots[pair*2+1].page;mix[pair]=targets[pair]=b>a?1:0;}
        if(hasSelection)targets[Math.floor(clock.active/2)]=mix[Math.floor(clock.active/2)]=clock.active%2;
        boards.forEach(b=>{b.last='';b.wet=null;});eraserReturn=null;eraserPickup=null;eraser.userData.state='resting';
        previousTip=null;wipeCanvas.width=W;wipeSamples=0;particles.forEach(p=>p.life=0);particlePositions.fill(-10000);
        hydrating=false;update(0,true);
      }catch(error){if(epoch===renderEpoch){loadingError=error;hydrating=false;}}
    },
    get navigation(){return navigation;},get seeking(){return seeking;},reports,viewScale:options.viewScale||.72,get pages(){return pages;},get clock(){return clock;},get report(){return activeReport;},consoleButtons,reportButtons,hoverTargets:[...touchButtons,reportHeader.mesh],setConsoleState,
    get pendingReport(){return pendingReport;},
    preloadReports:()=>Promise.allSettled(reports.map(prepareReport)),
    reportFocus:()=>scene.localToWorld(new THREE.Vector3(reportX+1.1,2.45,-11.34)),
    async setReport(id){
      const next=reports.find(r=>r.id===id);if(!next)throw new Error('未知报告');
      seekRequest++;seeking=false;const request=++reportRequest;pendingReport=next;setReportState();
      try{
        const manifest=await prepareReport(next);if(request!==reportRequest)return false;
        // Keep the current talk intact until its replacement cover is available.
        generation++;navigation=manifest.navigation;pages=manifest.pages;activeReport=next;clock=new LectureClock(pages.length);estimateDurations();hasSelection=true;if(navigation?.sections)clock.stopAt=navigation.sections[0].end;loadingError=null;
        cache.clear();pending.clear();guides.clear();erasePlans.clear();pageRows.clear();wipeCanvas.width=W;wipeSamples=0;
        boards.forEach(b=>{b.last='';b.wet=null;});targets.fill(0);eraserReturn=null;eraserPickup=null;eraser.visible=false;eraser.userData.state='parked';
        parkedErasers.forEach(e=>e.visible=true);chalk.visible=false;previousTip=null;lastWritePage=-1;wear=0;particles.forEach(p=>p.life=0);particlePositions.fill(-10000);dustGeometry.attributes.position.needsUpdate=true;
        playing=true;version++;await load(0,manifest.cover);
        if(request!==reportRequest)return false;
        // A new report starts on a clean board; there is no previous page to lift or erase.
        clock.startWrite();boards.forEach((_,i)=>draw(i));return true;
      }catch(error){if(request!==reportRequest)return false;throw error;}
      finally{if(request===reportRequest){pendingReport=null;setReportState();}}
    },
    setWritingSpeed(value){writingSpeed=Math.max(.25,Math.min(2,Number(value)||1));},
    get writingSpeed(){return writingSpeed;},
    get language(){return language;},copy:(index=clock.page)=>chalkCopy(pages[index],language),
    async setLanguage(value){
      const next=value==='en'?'en':'zh';if(next===language)return;
      seekRequest++;seeking=false;language=next;seminarScreen?.setLanguage(next);setConsoleState();setReportState();generation++;loadingError=null;cache.clear();pending.clear();guides.clear();erasePlans.clear();pageRows.clear();wipeCanvas.width=W;wipeSamples=0;previousTip=null;
      boards.forEach(b=>{b.last='';b.wet=null;});version++;
      try{await Promise.all([...new Set([clock.page,...clock.slots.map(s=>s.page)])].map(index=>load(index)));}
      catch(error){loadingError=error;throw error;}version++;
    },
    setRange(start=0,end=pages.length-1){hasSelection=true;seminarScreen?.select(navigation?.sections?.find(s=>s.start===start)?.id);clock.startAt=Math.max(0,Math.min(start,pages.length-1));clock.stopAt=Math.max(clock.startAt,Math.min(end,pages.length-1));return seek(start);},
    status:()=>loadingError?loadingError.message:!hasSelection?'请在左侧智慧屏选择本次内容':`${clock.page-clock.startAt+1} / ${clock.stopAt-clock.startAt+1} · ${clock.ended?(navigation?.sections?'本节结束':'报告结束'):phaseNames[clock.phase]} · ${chalkCopy(pages[clock.page],language).title}`,
    get playing(){return hasSelection&&playing&&!clock.ended;},set playing(value){playing=hasSelection&&value;},
    select,step(delta){const next=Math.max(0,Math.min(pages.length-1,clock.page+delta));if(next!==clock.page)select(next);},rewrite(){select(clock.page);},staticPage,
    lift(pair,value){targets[pair]=THREE.MathUtils.clamp(Number(value),0,1);},
    heights:()=>[...targets],focus:(single=false)=>scene.localToWorld(new THREE.Vector3(boards[clock.active].group.position.x,single?boards[clock.active].group.position.y:(BOARD_LAYOUT.low+BOARD_LAYOUT.high)/2,-10.4+BOARD_MOUNT_OFFSET)),
    dispose(){renderEpoch++;seminarScreen?.dispose();hardware.dispose();reportTextures.forEach(t=>t.dispose());[reportHeader.mesh,...reportButtons].forEach(b=>b.traverse(o=>{o.geometry?.dispose();o.material?.dispose();}));trayChalkGeometry.dispose();trayChalkMaterials.forEach(m=>m.dispose());consoleTextures.forEach(t=>t.dispose());consoleButtons.forEach(b=>b.traverse(o=>{o.geometry?.dispose();o.material?.dispose();}));dustGeometry.dispose();dustMaterial.dispose();dotMap.dispose();chalk.geometry.dispose();chalk.material.dispose();eraser.geometry.dispose();felt.geometry.dispose();felt.material.dispose();boards.forEach(board=>{board.texture.dispose();board.roughTexture.dispose();board.group.traverse(object=>{object.geometry?.dispose();object.material?.dispose();});});cache.clear();guides.clear();}
  };
}
