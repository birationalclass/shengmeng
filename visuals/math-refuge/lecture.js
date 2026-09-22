import * as THREE from 'three';
import {LectureClock,boardHeights} from './lecture-state.js?v=30-seminar';
import {inkGuides,inkReveal,writingPose,writingPlan,erasingPlan,eraserPose,wetOpacity,chalkLength,DRY_SECONDS,ERASER_HALF_WIDTH as EW,ERASER_HALF_HEIGHT as EH} from './chalk-motion.js?v=22-handwritten-cover';

import {chalkCopy,composeChalkPage} from './chalk-language.js?v=32-report-position';

import {REPORTS} from './report-catalog.js?v=32-report-position';

const W=1536,H=640,BOARD_W=5.3,BOARD_H=2.05;
const phaseNames={lift:'升降换板',erase:'擦除板书',write:'粉笔书写',hold:'停留阅读'};
export async function createLecture(scene,renderer){
  let activeReport=REPORTS.find(report=>report.id==='hu');
  const response=await fetch(activeReport.manifest+'?v=32-report-position');
  if(!response.ok)throw new Error('Unable to load the opening report');
  let {pages}=await response.json(),clock=new LectureClock(pages.length);
  const cache=new Map(),pending=new Map(),guides=new Map(),erasePlans=new Map(),pageRows=new Map();let loadingError=null,version=0,language='zh',generation=0;
  if(document.fonts)await Promise.all([document.fonts.load('42px RefugeChinese'),document.fonts.load('42px RefugeLatin'),document.fonts.load('42px RefugeMath')]);
  function load(index){
    if(index<0)return Promise.resolve(null);
    if(cache.has(index))return Promise.resolve(cache.get(index));
    if(pending.has(index))return pending.get(index);
    const epoch=generation,lang=language;
    const job=new Promise((resolve,reject)=>{
      const image=new Image();image.onload=()=>{
        if(epoch!==generation){resolve(null);return;}
        const sample=document.createElement('canvas');sample.width=W;sample.height=H;const sampleCtx=sample.getContext('2d',{willReadFrequently:true});
        const rows=composeChalkPage(sampleCtx,pages[index],index,lang,image);pageRows.set(index,rows);
        cache.set(index,sample);pending.delete(index);version++;
        let pixels=null;try{if(sampleCtx.getImageData)pixels=sampleCtx.getImageData(0,0,W,H);}catch{ /* Measured text bounds remain a safe fallback. */ }
        if(pixels)guides.set(index,inkGuides(pixels,rows));
        const wipe=erasingPlan(pixels,rows);erasePlans.set(index,wipe);
        clock.setDurations(index,{write:Math.max(.8,writingPlan(rows,guides.get(index)).duration),erase:Math.max(.4,wipe.duration),hold:pages[index].kind==='cover'?16:8});
        // Retain six on-board pages and the active/next page, evict other SVGs.
        const keep=new Set([...clock.slots.map(s=>s.page),clock.page,Math.min(clock.page+1,pages.length-1)]);
        for(const key of cache.keys())if(cache.size>10&&!keep.has(key)){cache.delete(key);guides.delete(key);erasePlans.delete(key);pageRows.delete(key);}
        resolve(sample);
      };image.onerror=()=>{if(epoch!==generation){resolve(null);return;}pending.delete(index);reject(new Error('板书资源加载失败，请刷新重试。'));};image.src=pages[index].formulaAsset+'?v=32-report-position';
    });pending.set(index,job);return job;
  }
  await load(0);
  const boards=[],mix=[0,0,0],targets=[0,0,0];let playing=true,accumulator=0,writingSpeed=1;
  const frameMaterial=new THREE.MeshStandardMaterial({color:'#735c3e',roughness:.65});
  const metal=new THREE.MeshStandardMaterial({color:'#ad9d87',roughness:.84,metalness:.25,envMapIntensity:.25});
  const wall=new THREE.Mesh(new THREE.BoxGeometry(17.2,4.8,.16),new THREE.MeshStandardMaterial({color:'#102421',roughness:1}));
  wall.position.set(28,2.65,-10.82);wall.name='Six-board lecture wall';scene.add(wall);
  const cube=new THREE.BoxGeometry(1,1,1);
  const trayChalkGeometry=new THREE.CylinderGeometry(.018,.015,.16,10);
  const trayChalkMaterials=['#f5efdc','#e9aa24','#e75575','#339bdd'].map(color=>new THREE.MeshStandardMaterial({color,roughness:1,emissive:color,emissiveIntensity:.18}));
  function part(parent,p,s,material){const mesh=new THREE.Mesh(cube,material);mesh.position.fromArray(p);mesh.scale.fromArray(s);parent.add(mesh);return mesh;}
  for(let pair=0;pair<3;pair++){
    const x=22.4+pair*5.6;
    for(const dx of [-2.76,2.76])part(scene,[x+dx,2.7,-10.6],[.045,4.75,.09],metal);
    for(let side=0;side<2;side++){
      const group=new THREE.Group();group.position.set(x,boardHeights(0)[side],-10.45+side*.16);
      group.name=`Sliding chalkboard ${pair+1}${side?'B':'A'}`;scene.add(group);
      const canvas=document.createElement('canvas');canvas.width=W;canvas.height=H;
      const ctx=canvas.getContext('2d'),texture=new THREE.CanvasTexture(canvas);texture.colorSpace=THREE.SRGBColorSpace;
      texture.anisotropy=Math.min(8,renderer.capabilities.getMaxAnisotropy());texture.generateMipmaps=true;texture.minFilter=THREE.LinearMipmapLinearFilter;
      const roughCanvas=document.createElement('canvas');roughCanvas.width=W/4;roughCanvas.height=H/4;const roughCtx=roughCanvas.getContext('2d');roughCtx.fillStyle='white';roughCtx.fillRect(0,0,W/4,H/4);
      const roughTexture=new THREE.CanvasTexture(roughCanvas);
      const surface=new THREE.Mesh(new THREE.PlaneGeometry(BOARD_W,BOARD_H),new THREE.MeshPhysicalMaterial({map:texture,color:'#c9c5bb',roughness:1,roughnessMap:roughTexture,metalness:0,specularIntensity:0,envMapIntensity:0,emissive:0x000000,emissiveIntensity:0}));
      group.add(surface);
      for(const y of [-BOARD_H/2,BOARD_H/2])part(group,[0,y,.025],[BOARD_W+.1,.07,.11],frameMaterial);
      for(const px of [-BOARD_W/2,BOARD_W/2])part(group,[px,0,.025],[.07,BOARD_H,.11],frameMaterial);
      part(group,[0,-BOARD_H/2-.07,.06],[.55,.05,.09],metal);
      boards.push({group,canvas,ctx,texture,roughCtx,roughTexture,wet:null,last:''});
    }
    part(scene,[x,.33,-10.2],[5.4,.07,.23],frameMaterial);
    part(scene,[x,.385,-10.085],[5.4,.04,.025],metal);
    for(let j=0;j<4;j++){
      const stick=new THREE.Mesh(trayChalkGeometry,trayChalkMaterials[j]);stick.name=`Tray chalk ${pair+1} ${j+1}`;
      stick.rotation.z=Math.PI/2;stick.rotation.y=(j%2?1:-1)*.08;stick.position.set(x-.95+j*.24,.383,-10.2);
      stick.userData={column:pair,colorIndex:j};scene.add(stick);
    }
  }
  // One synchronized glass toggle below each board column. Align all three
  // toward the right of their column so the middle control clears the glass joint.
  const consoleButtons=[],consoleTextures=[];
  const touchCanvas=document.createElement('canvas');touchCanvas.width=1024;touchCanvas.height=384;
  const touchTexture=new THREE.CanvasTexture(touchCanvas);touchTexture.colorSpace=THREE.SRGBColorSpace;consoleTextures.push(touchTexture);
  for(let column=0;column<3;column++){
    const button=new THREE.Mesh(new THREE.PlaneGeometry(2.2,.65),new THREE.MeshBasicMaterial({color:'#7be7df',transparent:true,opacity:0,depthWrite:false,toneMapped:false}));
    button.name=`Smart glass language touch surface ${column+1}`;button.position.set(23.9+column*5.6,-.16,-11.34);
    button.userData={action:'language',column,pressed:false,restZ:-11.34,lastLabel:'',smartGlass:true,singleToggle:true,glassPanel:column===0?1:2,canvas:touchCanvas,texture:touchTexture};
    const label=new THREE.Mesh(new THREE.PlaneGeometry(2.16,.60),new THREE.MeshBasicMaterial({map:touchTexture,transparent:true,opacity:1,depthWrite:false,toneMapped:false}));
    label.position.z=.008;button.add(label);scene.add(button);consoleButtons.push(button);
  }
  function setConsoleState(){
    if(consoleButtons.every(button=>button.userData.lastLabel===language))return;
    for(const button of consoleButtons)button.userData.lastLabel=language;
    const c=touchCanvas.getContext('2d');c.clearRect(0,0,1024,384);
    c.textAlign='center';c.shadowColor='#4fe3d8';c.shadowBlur=12;
    c.font='600 184px "PingFang SC", sans-serif';c.fillStyle='#ffffff';
    c.fillText(language==='zh'?'EN  ↔':'中文  ↔',512,250);
    c.shadowBlur=0;c.fillStyle='#d9fff7';c.fillRect(290,316,444,7);
    touchTexture.needsUpdate=true;
  }
  const reportButtons=[],reportTextures=[];
  // Keep the full-size touch targets beside the board frame (0.15 local units clear).
  const reportX=16.9;
  function glassLabel(width,height,x,y,name){
    const canvas=document.createElement('canvas');canvas.width=1024;canvas.height=240;
    const texture=new THREE.CanvasTexture(canvas);texture.colorSpace=THREE.SRGBColorSpace;reportTextures.push(texture);
    const mesh=new THREE.Mesh(new THREE.PlaneGeometry(width,height),new THREE.MeshBasicMaterial({map:texture,transparent:true,depthWrite:false,toneMapped:false}));
    mesh.position.set(x,y,-11.332);mesh.name=name;scene.add(mesh);return {mesh,canvas,texture};
  }
  const reportHeader=glassLabel(4.6,.55,reportX,3.85,'Smart glass report heading');
  for(const [index,report] of REPORTS.entries()){
    const label=glassLabel(4.6,.9,reportX,2.95-index*1.1,`Smart glass report ${report.id}`);
    const button=new THREE.Mesh(new THREE.PlaneGeometry(4.7,1.02),new THREE.MeshBasicMaterial({transparent:true,opacity:0,depthWrite:false,toneMapped:false,color:'#7be7df'}));
    button.position.set(reportX,2.95-index*1.1,-11.34);button.name=`Report selection ${report.speaker}`;
    scene.remove(label.mesh);label.mesh.position.set(0,0,.008);button.add(label.mesh);scene.add(button);
    button.userData={action:`report:${report.id}`,reportId:report.id,smartGlass:true,pressed:false,canvas:label.canvas,texture:label.texture};reportButtons.push(button);
  }
  function setReportState(){
    const header=reportHeader.canvas.getContext('2d');header.clearRect(0,0,1024,240);header.textAlign='right';header.fillStyle='#c5f8ef';header.font='500 66px "PingFang SC", sans-serif';
    header.fillText(language==='zh'?'报告人 / 报告主题':'SPEAKER / TOPIC',996,154);reportHeader.texture.needsUpdate=true;
    for(const [index,button] of reportButtons.entries()){
      const report=REPORTS[index],selected=report.id===activeReport.id,c=button.userData.canvas.getContext('2d');
      c.clearRect(0,0,1024,240);c.textAlign='right';c.shadowColor='#56e4d4';c.shadowBlur=selected?8:2;c.fillStyle=selected?'#fff2cf':'#e5fff8';
      c.font='600 78px "PingFang SC", sans-serif';c.fillText(language==='zh'?report.speaker:report.speakerEn,996,91);
      c.shadowBlur=0;c.font='400 37px "PingFang SC", sans-serif';c.fillStyle='#d2f5e9';
      const topic=language==='zh'?report.topic:report.topicEn,words=language==='zh'?[...topic]:topic.split(/(?<= )/);let line='',y=159;
      for(const word of words){if(c.measureText(line+word).width>960){c.fillText(line,996,y);line=word;y+=47;}else line+=word;}c.fillText(line,996,y);
      if(selected){c.fillStyle='#f4d6a1';c.fillRect(816,224,180,4);}button.userData.texture.needsUpdate=true;button.userData.selected=selected;
    }
  }
  const touchButtons=[...consoleButtons,...reportButtons];
  setConsoleState();setReportState();
  const chalk=new THREE.Mesh(new THREE.CylinderGeometry(.017,.014,.17,8),new THREE.MeshStandardMaterial({color:'#f3edda',roughness:1,metalness:0,emissive:'#e3dcc8',emissiveIntensity:.32,envMapIntensity:.15}));
  const chalkAxis=new THREE.Vector3(.22,-.42,.88).normalize();chalk.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0),chalkAxis);chalk.name='Writing chalk';scene.add(chalk);
  const eraserWidth=EW*2/W*BOARD_W,eraserHeight=EH*2/H*BOARD_H;
  const eraser=new THREE.Mesh(new THREE.BoxGeometry(eraserWidth,eraserHeight,.08),frameMaterial);eraser.name='Moving blackboard eraser';scene.add(eraser);
  const felt=new THREE.Mesh(new THREE.BoxGeometry(eraserWidth*.98,eraserHeight*.98,.025),new THREE.MeshStandardMaterial({color:'#353d36',roughness:1}));felt.position.z=-.0475;eraser.add(felt);
  const parkedErasers=Array.from({length:3},(_,column)=>{
    const parked=eraser.clone();parked.name=`Tray eraser ${column+1}`;parked.position.set(23.25+column*5.6,.430,-10.2);parked.rotation.set(-Math.PI/2,0,.035);
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
    if(board.last===key)return;board.last=key;
    ctx.drawImage(grain,0,0);const image=cache.get(slot.page);
    if(image){
      const rows=pageRows.get(slot.page)||pages[slot.page].rows;
      // Reveal each complete mathematical row left to right, preserving exact
      // SVG fractions/superscripts. The grain is deterministic, never flickering.
      rows.forEach(([x,y,w,h],row)=>{
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
  function update(dt,reduced=false){
    dt=Math.max(0,Math.min(.1,dt));for(const b of touchButtons)b.material.opacity=THREE.MathUtils.damp(b.material.opacity,b.userData.pressed?.08:0,18,dt);if(playing&&!reduced)effectTime+=dt;
    const oldPhase=clock.phase,oldActive=clock.active;
    const ready=cache.has(clock.page)&&(clock.slots[clock.active].page<0||cache.has(clock.slots[clock.active].page));
    if(!ready&&!loadingError){load(clock.page).catch(error=>{loadingError=error;});load(clock.slots[clock.active].page).catch(error=>{loadingError=error;});}
    // Ink removal only starts after the felt reaches the board from its tray.
    const collectingEraser=clock.phase==='erase'&&eraser.userData.state!=='erasing';
    if(playing&&ready&&!loadingError&&!reduced&&!collectingEraser){
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
        positionTool(eraserContact,p.x,p.y);eraserContact.position.z+=.047+p.lift;eraserContact.rotation.set(.03,0,-p.angle);
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
      const tip=chalk.position.clone();
      if(previousTip&&pose.contact)wear+=Math.min(.07,tip.distanceTo(previousTip))*.007;
      const length=chalkLength(wear),propScale=1/(scene.scale.y||1);chalk.scale.set(propScale,length/.17*propScale,propScale);chalk.position.addScaledVector(chalkAxis,length*propScale/2);chalk.userData.length=length;chalk.userData.contact=pose.contact;previousTip=tip;
      dustAccumulator+=dt;
      if(pose.contact&&dustAccumulator>.09){dustAccumulator=0;const i=particleCursor++%particleCount;particles[i]={life:1.1,vx:(random()-.5)*.025,vy:-.015};particlePositions.set([tip.x,tip.y,tip.z+.016],i*3);}
    }else previousTip=null;
    if(erasing&&!eraserPickup){const p=eraserPose(clock.progress,W,H,boards[clock.active].wet?.plan);positionTool(eraser,p.x,p.y);eraser.position.z+=.047+p.lift;eraser.rotation.set(.03,0,-p.angle);}
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
  function staticPage(){clock.startWrite();clock.slots[clock.active].progress=1;clock.phase='hold';clock.elapsed=0;clock.ended=clock.page===pages.length-1;version++;}
  boards.forEach((_,i)=>draw(i));
  return {
    update,get pages(){return pages;},get clock(){return clock;},get report(){return activeReport;},consoleButtons,reportButtons,setConsoleState,
    reportFocus:()=>scene.localToWorld(new THREE.Vector3(reportX+1.1,2.25,-11.34)),
    async setReport(id){
      const next=REPORTS.find(r=>r.id===id);if(!next)throw new Error('未知报告');
      const response=await fetch(next.manifest+'?v=32-report-position');if(!response.ok)throw new Error('报告加载失败，请重试。');
      const manifest=await response.json();if(!manifest.pages?.length)throw new Error('报告内容为空');
      // Keep the current talk intact until its replacement cover is available.
      await new Promise((resolve,reject)=>{const image=new Image();image.onload=resolve;image.onerror=()=>reject(new Error('报告封面加载失败，请重试。'));image.src=manifest.pages[0].formulaAsset;});
      generation++;pages=manifest.pages;activeReport=next;clock=new LectureClock(pages.length);loadingError=null;
      cache.clear();pending.clear();guides.clear();erasePlans.clear();pageRows.clear();wipeCanvas.width=W;wipeSamples=0;
      boards.forEach(b=>{b.last='';b.wet=null;});targets.fill(0);eraserReturn=null;eraserPickup=null;eraser.visible=false;eraser.userData.state='parked';
      parkedErasers.forEach(e=>e.visible=true);chalk.visible=false;previousTip=null;lastWritePage=-1;wear=0;particles.forEach(p=>p.life=0);particlePositions.fill(-10000);dustGeometry.attributes.position.needsUpdate=true;
      playing=true;version++;setReportState();await load(0);boards.forEach((_,i)=>draw(i));
    },
    setWritingSpeed(value){writingSpeed=Math.max(.25,Math.min(2,Number(value)||1));},
    get writingSpeed(){return writingSpeed;},
    get language(){return language;},copy:(index=clock.page)=>chalkCopy(pages[index],language),
    async setLanguage(value){
      const next=value==='en'?'en':'zh';if(next===language)return;
      language=next;setConsoleState();setReportState();generation++;loadingError=null;cache.clear();pending.clear();guides.clear();erasePlans.clear();pageRows.clear();wipeCanvas.width=W;wipeSamples=0;previousTip=null;
      boards.forEach(b=>{b.last='';b.wet=null;});version++;
      try{await Promise.all([...new Set([clock.page,...clock.slots.map(s=>s.page)])].map(load));}
      catch(error){loadingError=error;throw error;}version++;
    },
    status:()=>loadingError?loadingError.message:`${clock.page+1} / ${pages.length} · ${clock.ended?'报告结束':phaseNames[clock.phase]} · ${chalkCopy(pages[clock.page],language).title}`,
    get playing(){return playing&&!clock.ended;},set playing(value){playing=value;},
    select,step(delta){const next=Math.max(0,Math.min(pages.length-1,clock.page+delta));if(next!==clock.page)select(next);},rewrite(){select(clock.page);},staticPage,
    lift(pair,value){targets[pair]=THREE.MathUtils.clamp(Number(value),0,1);},
    heights:()=>[...targets],focus:(single=false)=>scene.localToWorld(new THREE.Vector3(boards[clock.active].group.position.x,single?boards[clock.active].group.position.y:2.6,-10.4)),
    dispose(){reportTextures.forEach(t=>t.dispose());[reportHeader.mesh,...reportButtons].forEach(b=>b.traverse(o=>{o.geometry?.dispose();o.material?.dispose();}));trayChalkGeometry.dispose();trayChalkMaterials.forEach(m=>m.dispose());consoleTextures.forEach(t=>t.dispose());consoleButtons.forEach(b=>b.traverse(o=>{o.geometry?.dispose();o.material?.dispose();}));dustGeometry.dispose();dustMaterial.dispose();dotMap.dispose();chalk.geometry.dispose();chalk.material.dispose();eraser.geometry.dispose();felt.geometry.dispose();felt.material.dispose();boards.forEach(board=>{board.texture.dispose();board.roughTexture.dispose();board.group.traverse(object=>{object.geometry?.dispose();object.material?.dispose();});});cache.clear();guides.clear();}
  };
}
