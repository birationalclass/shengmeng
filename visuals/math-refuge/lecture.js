import {classroomWaitAt,countdownTextRect,createCountdownTargets,placeCountdownTarget} from './board-countdown.js';
import {prepareMaliChalk} from './mali-chalk.js?v=safari-glyph-20261019-1';
import {AssetRetry} from './asset-retry.js';
import {boardInkScale} from './board-ink-resolution.js';
import {changedInkRect,unionInkRects,intersectsInk,createBoardInkUploader} from './board-ink-update.js?v=safari-glyph-20261019-1';
import {preparationTurn} from './preparation-turn.js';
import {createBoardTrayHardware} from './board-tray.js?v=crystal-black-b2';
import {isCrystalScheme,paintStoneBoard,setTrackScheme} from './board-mineral.js';
import {placeTrayControl,TRAY_STORAGE} from './board-tray-layout.js';
import {createStudentLottery,drawStudentLottery,lotteryHitTargets,LOTTERY_RECT} from './student-lottery.js';
import {createCoursePreload} from './course-preload.js';
import {prepareBoardAssets} from './board-assets.js';
import {prepareInlineMath} from './chalk-inline-math.js?v=mali-20261017';
import {LessonBudget} from './lesson-budget.js?v=sylow-two-lessons-20261015';
import {narrationHighlights,measuredHighlight,highlightFrame,createBoardHighlight} from './board-highlight.js?v=smart-voice-9';
import {createBoardPageControls} from './board-page-control.js?v=unframed-controls-1';
import {drawClassroomActivity,classroomActivityAt,classroomCountdown} from './classroom-board.js?v=mali-20261017';
import {boardCameraFrame,stepBoardCameraZoom} from './board-camera-framing.js';
import {createBoardCameraControl} from './board-camera-control.js?v=unframed-controls-1';
import {boardContentJump,advanceBoardQueue} from './board-transition.js';
import {drawClassroomMetadata} from './classroom-metadata.js?v=sylow-two-lessons-20261015';
import {createBoardTimePanel} from './board-time.js?v=unframed-controls-1';
import {SCREEN_FONT,SCREEN_MONO,SCREEN_COLORS,CONTROL_VISUAL_SCALE} from './smart-screen-style.js?v=unframed-controls-1';
import {createReportVoice,createBoardVoicePanel,reportControlLayout,mapNarrationPosition,narrationFrame,syncNarrationClock,bindVoiceFocusPause} from './report-voice.js?v=uniform-review-20261019';
import {BoardStorage} from './board-storage.js?v128';
import {BOARD_SHAFT,BUILDING_SCALE,DECK_Y,LECTURE_SCALE,LECTURE_LIFT} from './site-layout.js?v124';
import {createSmartGlassHub} from './smart-glass-hub.js?v=smart-voice-9';
import {withDeadline,decodeImage} from './mobile-runtime.js?v79-mobile';
import {authoredContext,authoredFormula} from './authored-chalk.js?v=mali-20261017';
import {createChineseChalk,paintChineseGroup} from './chinese-chalk.js?v=safari-glyph-20261019-1';
import {eraserTransfer} from './eraser-transfer.js?v67-dark-sky';
import {createSeminarScreen} from './seminar-screen.js?v=report-line-sync-6';
import * as THREE from 'three';
import {LectureClock,boardSlot,boardHeights,boardFaceZ,BOARD_LAYOUT} from './lecture-state.js?v=uniform-review-20261019';
import {inkGuides,inkReveal,strokeReveal,rasterStrokeReveal,writingPose,writingPlan,erasingPlan,eraserPose,wetOpacity,chalkLength,DRY_SECONDS,ERASER_HALF_WIDTH as EW,ERASER_HALF_HEIGHT as EH} from './chalk-motion.js?v=semantic-chalk-2';
import {paintChalkStroke} from './chalk-annotations.js?v=report-line-sync-6';
import {narrationWork,boardWorkFrame,writingSchedule,settledBoardFrame} from './board-work.js?v=uniform-review-20261019';
import {BoardReview,MIN_BOARD_REVIEW_SECONDS} from './board-review.js?v=uniform-review-20261019';
import {stampFelt} from './eraser-contact.js';

import {chalkCopy,chalkPageText,composeChalkPage} from './chalk-language.js?v=mali-20261017';

import {REPORTS} from './report-catalog.js?v=ye2-report-14';
import {CLASSROOM_PROGRAMS} from './classroom-catalog.js?v=sylow-two-lessons-20261015';
import {createHallProgramScreen} from './hall-program-screen.js?v=sylow-two-lessons-20261015';
import {createReportLoader} from './report-loader.js?v=report-line-sync-6';

import {createBoardHardware,TRAY,BOARD_MOUNT_OFFSET} from './board-hardware.js?v=43-tight-boards';
import {silverInk,seminarDate,addTextSheen,updateTextSheen} from './smart-screen.js?v=crystal-black-b2';

const W=1536,H=640,BOARD_W=BOARD_LAYOUT.width,BOARD_H=BOARD_LAYOUT.height;
const phaseNames={lift:'升降换板',erase:'擦除板书',write:'粉笔书写',hold:'停留阅读'};
export async function createLecture(scene,renderer,options={}){
  const reportProgress=options.onProgress||(()=>{});
  const pixelScale=options.boardScale===.5?.5:1;const inkUploader=createBoardInkUploader(THREE,renderer);let lastRasterMs=0,lookaheadAt=0;
  const disabled=Boolean(options.disabled),canAuthor=typeof document.createElementNS==='function'&&typeof window!=='undefined';let writingStyle=['refined','marck'].includes(options.writingStyle)?options.writingStyle:'mali-italic',mathStyle=options.mathStyle==='refined'?'refined':'mali-italic';const boardMipBias={value:0};
  const reports=disabled?[{id:'unavailable',speaker:'',speakerEn:'',topic:'',topicEn:'',url:'',sourceLabel:''}]:options.reports||[...REPORTS,...CLASSROOM_PROGRAMS];
  let activeReport=reports.find(report=>report.id===(options.defaultReport||'hu'))||reports[0];
  const studentLottery=createStudentLottery();studentLottery.setCourse(activeReport.courseId||activeReport.id,activeReport.id);const assetPreload=createCoursePreload();const prepareReport=createReportLoader(),openingReport=disabled?{pages:[{kind:'closing',title:'',source:'',text:'',en:{title:'',source:'',text:''},rows:[]}]}:await prepareReport(activeReport);
  reportProgress(.25);
  let voiceEnabled=true,voiceTone='original',voiceBookmark=null,highlightEnabled=options.highlight!==false,highlightState=null,highlightManifest=null,highlightSpecs=[];const measuredHighlights=new Map();
  let navigation=openingReport.navigation;
  let pages=openingReport.pages,clock=new LectureClock(pages.length),reportRequest=0,pendingReport=null,seekRequest=0,seeking=false;
  let requestedPage=null,seekPinned=new Set(),hasSelection=!disabled&&!options.requireSelection,present=true,renderActive=true,hydrating=false,renderEpoch=0;
  let screenHub=null,openingDemo=null,openingSurfacesReady=false,translating=false,languageRequest=0,translatedInk=null;
  let storageRig=null,stored=Boolean(options.retractable&&options.startStored),storageProgress=stored?1:0,storageLabel=null,storageLabelText='';
  const storageMotion=new BoardStorage(stored),storageLids=[];let storageWell=null,storageCap=null;
  const estimateDurations=()=>pages.forEach((p,i)=>clock.setDurations(i,{write:p.kind?12:Math.max(23,18+(p.text?.length||0)*.24+(p.tex?.length||0)*.07),erase:24,hold:MIN_BOARD_REVIEW_SECONDS}));
  estimateDurations();
  const cache=new Map(),pending=new Map(),guides=new Map(),erasePlans=new Map(),pageRows=new Map();const assetRetry=new AssetRetry();let boardPreparation=null;let loadingError=null,version=0,language=options.initialLanguage==='zh'?'zh':'en',generation=0;
  let fontsReady=0;
  if(document.fonts&&!disabled)await withDeadline(Promise.all(['42px RefugeChinese','42px RefugeLatin','42px RefugeMath','42px RefugeMathSymbols'].map(font=>document.fonts.load(font).then(result=>{reportProgress(.25+(++fontsReady)/4*.45);return result;}))),15000,'板书字体加载');
  let chineseChalk=null;
  const lessonBudget=new LessonBudget(),omittedProofPages=new Set();let proofJumping=false;
  const boardReview=new BoardReview(),revealedPages=new Set();
  let boardWork=null,eraseRun=null,previousNarrationTime=null,workManifest=null;const completedWork=new Set(),exerciseChoices=new Map(),exerciseFrames=new Map(),exerciseEraseKeys=new Map();
  function currentExercise(index=clock.page){if(pages[index]?.exerciseBoard)return null;const b=voice.manifest?.boards.find(b=>b.page===index);return activeReport.kind==='classroom'&&b?classroomActivityAt(voice.manifest,Math.min(voice.state.time,b.end-.001),index):null;}
  function stepExercise(delta){const a=currentExercise(),frame=exerciseFrames.get(clock.page);if(!a||!frame)return false;const next=frame.sheetIndex+delta;if(next<0||next>=frame.sheetCount)return false;exerciseChoices.set(a.start+':'+a.feedback,next);boards.forEach(b=>b.last='');return true;}
  async function omitOptionalProof(){const optional=voice.manifest?.boards.filter(b=>b.optionalProof)||[];if(!optional.length||proofJumping)return false;proofJumping=true;lessonBudget.decision='skip';optional.forEach(b=>omittedProofPages.add(b.page));cancelBoardWork();highlighter.hide();highlightState=null;try{await voice.seek(optional.at(-1).end,{preservePlayback:true});version++;return true;}finally{proofJumping=false;}}
  function cancelBoardWork(){translatedInk=null;boardWork?.resolve();boardWork=null;eraseRun=null;previousNarrationTime=null;workManifest=null;completedWork.clear();boardReview.clear();revealedPages.clear();}
  function clearPageCache(){cancelBoardWork();assetRetry.clear();boardPreparation=null;exerciseChoices.clear();exerciseFrames.clear();exerciseEraseKeys.clear();for(const c of cache.values()){c.width=1;c.height=1;}cache.clear();}
  function load(index,preparedImage,{background=false}={}){
    if(index<0)return Promise.resolve(null);
    if(cache.has(index))return Promise.resolve(cache.get(index));
    if(pending.has(index)){if(!background)void prepareBoardAssets(pages[index]).catch(()=>{});return pending.get(index);}
    const blocked=assetRetry.blocked(index);if(blocked)return blocked;
    const epoch=generation,lang=language,style=writingStyle,formulaStyle=mathStyle;
    let timed;const stage=label=>{if(timed)timed.stage=label;};const job=new Promise((resolve,reject)=>{
      let image=preparedImage||new Image();const ready=async()=>{try{
        if(epoch!==generation){resolve(null);return;}
        const sample=document.createElement('canvas');sample.width=W;sample.height=H;const sampleCtx=sample.getContext('2d',{willReadFrequently:true});
        let rows;
        if(pages[index].orderedBoard){
          const {prepareBoard}=await import('./sylow-f-renderer.js?v=safari-glyph-20261019-1');
          const prepared=await prepareBoard(pages[index].orderedBoard,lang);
          if(epoch!==generation){resolve(null);return;}
          sampleCtx.drawImage(prepared.canvas,0,0);rows=prepared.rows;
        }else{
        let chinese=null;stage('中文字形准备');
        if(lang==='zh'&&canAuthor){if(!chineseChalk)chineseChalk=createChineseChalk().catch(error=>{chineseChalk=null;throw error;});chinese=await (await chineseChalk).prepare(chalkPageText(pages[index],lang));if(epoch!==generation){resolve(null);return;}}
        await preparationTurn({background:background&&index!==clock.page&&index!==requestedPage});
        stage('Mali 字形准备');if(canAuthor&&(style==='mali-italic'||formulaStyle==='mali-italic'))await prepareMaliChalk(chalkPageText(pages[index],lang));
        stage('公式笔画解析');await prepareInlineMath(chalkPageText(pages[index],lang),formulaStyle);
        await preparationTurn({background:background&&index!==clock.page&&index!==requestedPage});
        if(epoch!==generation||pending.get(index)!==timed){resolve(null);return;}
        stage('排版与擦除规划');const recorder=canAuthor?authoredContext(sampleCtx,chinese,{latin:style!=='marck',latinStyle:style,mathStyle:formulaStyle}):null;rows=composeChalkPage(recorder?.ctx||sampleCtx,pages[index],index,lang,image,{deferStrokes:true,hideHeading:options.hideBoardHeadings,authored:Boolean(recorder),mathStyle:formulaStyle});if(recorder)rows=recorder.rows(rows);
        }
        pageRows.set(index,rows);
        await preparationTurn({background:background&&index!==clock.page&&index!==requestedPage});
        if(epoch!==generation||pending.get(index)!==timed){resolve(null);return;}
        let pixels=null;try{if(sampleCtx.getImageData)pixels=sampleCtx.getImageData(0,0,W,H);}catch{ /* Measured text bounds remain a safe fallback. */ }
        if(pixels)guides.set(index,inkGuides(pixels,rows));
        if(pages[index].exerciseBoard&&pixels){const c=document.createElement('canvas');c.width=W;c.height=H;const cx=c.getContext('2d');cx.putImageData(pixels,0,0);cx.fillStyle='white';cx.fillRect(...LOTTERY_RECT);pixels=cx.getImageData(0,0,W,H);}const wipe=erasingPlan(pixels,rows);erasePlans.set(index,wipe);
        clock.setDurations(index,{write:Math.max(.8,writingPlan(rows,guides.get(index)).duration),erase:Math.max(.4,wipe.duration),hold:MIN_BOARD_REVIEW_SECONDS});
        cache.set(index,sample);assetRetry.clear(index);if(pending.get(index)===timed)pending.delete(index);version++;
        // Retain six on-board pages and the active/next page, evict other SVGs.
        const keep=new Set([...seekPinned,...clock.slots.map(s=>s.page),clock.page,Math.min(clock.page+1,pages.length-1)]);
        for(const key of cache.keys())if(cache.size>(pixelScale<1?8:10)&&!keep.has(key)){cache.get(key).width=1;cache.get(key).height=1;cache.delete(key);guides.delete(key);erasePlans.delete(key);pageRows.delete(key);}
        resolve(sample);}catch(error){reject(error);}
      };
      const begin=()=>{stage('公式解析');if(pages[index].orderedBoard){queueMicrotask(ready);return;}if(preparedImage){queueMicrotask(ready);return;}
        if(canAuthor&&!pages[index].kind){authoredFormula(pages[index].formulaAsset+'?v=report-line-sync-6',{mathStyle:formulaStyle}).then(result=>{image=result;ready();},reject);return;}
        decodeImage(pages[index].formulaAsset+'?v=report-line-sync-6').then(result=>{image=result;ready();},reject);
      };
      if(pages[index].resourcePack)void prepareBoardAssets(pages[index],{background:background&&index!==clock.page&&index!==requestedPage}).then(begin,reject);else begin();
    });
    // A page can contain hundreds of healthy small transfers. Each request has
    // an aborting idle watchdog; a page-wide wall-clock race discarded slow but
    // successful preparation and left the selected board permanently stale.
    timed=job;timed.stage=pages[index].resourcePack?'资源包下载':'公式准备';pending.set(index,timed);timed.catch(error=>{if(pending.get(index)===timed){pending.delete(index);assetRetry.fail(index,error);}});return timed;
  }
  if(!disabled&&hasSelection)await load(0,openingReport.cover);
  reportProgress(1);
  if(navigation?.sections?.length)clock.stopAt=navigation.sections[0].end;
  const contentFadeQueue=[],boards=[],tracks=[],mix=[0,0,0],targets=[0,0,0];let playing=hasSelection&&!stored,accumulator=0,writingSpeed=1;
  const hardware=createBoardHardware(THREE),frameMaterial=hardware.wood;
  const metal=new THREE.MeshStandardMaterial({color:'#ad9d87',roughness:.84,metalness:.25,envMapIntensity:.25});
  const cube=new THREE.BoxGeometry(1,1,1);
  const trayHardware=createBoardTrayHardware(THREE,renderer.capabilities?.getMaxAnisotropy?.()||1);if(canAuthor)await trayHardware.loadGrain();
  const trayChalkGeometry=new THREE.CylinderGeometry(.018,.015,.16,10);
  const trayChalkMaterials=['#eee9d5','#e4cf9c','#ffada3','#93c9ff','#c3a1e8','#a4d5a0'].map(color=>new THREE.MeshStandardMaterial({color,roughness:1,emissive:color,emissiveIntensity:.18}));
  function part(parent,p,s,material){const mesh=new THREE.Mesh(cube,material);mesh.position.fromArray(p);mesh.scale.fromArray(s);parent.add(mesh);return mesh;}
  const blankCanvas=document.createElement('canvas');blankCanvas.width=128;blankCanvas.height=64;const blankCtx=blankCanvas.getContext('2d');blankCtx.fillStyle='#193d33';blankCtx.fillRect(0,0,128,64);
  const blankTexture=new THREE.CanvasTexture(blankCanvas);blankTexture.colorSpace=THREE.SRGBColorSpace;
  for(let pair=0;pair<3;pair++){
    const x=22.4+pair*5.6;
    const track=new THREE.Group();tracks.push(track);track.name='Double-channel lift track '+(pair+1);scene.add(track);
    track.position.z=BOARD_MOUNT_OFFSET;
    const channelDepths=[0,1].map(side=>boardFaceZ(side)-.035);
    track.userData={column:pair,depths:channelDepths.map(z=>z+BOARD_MOUNT_OFFSET),travel:[BOARD_LAYOUT.low,BOARD_LAYOUT.high],glassMounted:true};
    const railCenter=(BOARD_LAYOUT.railBottom+BOARD_LAYOUT.railTop)/2,railLength=BOARD_LAYOUT.railTop-BOARD_LAYOUT.railBottom+.06;
    for(const sign of [-1,1]){
      const railX=x+sign*2.745;
      for(const z of channelDepths){
        part(track,[railX+sign*.033,railCenter,z],[.022,railLength,.056],metal);
        for(const dz of [-.029,.029])part(track,[railX,railCenter,z+dz],[.055,railLength,.009],metal);
      }
      for(const y of [.62,railCenter,5.02]){
        part(track,[railX,y,boardFaceZ(0)-.085],[.065,.060,.14],metal);
        part(track,[railX,y,boardFaceZ(0)-.15],[.105,.13,.022],metal);
      }
    }
    for(const y of [BOARD_LAYOUT.railBottom,BOARD_LAYOUT.railTop]){const stop=part(track,[x,y,BOARD_LAYOUT.frontZ-BOARD_LAYOUT.channelGap/2-.025],[5.58,.045,BOARD_LAYOUT.channelGap+.09],metal);stop.name=y===BOARD_LAYOUT.railTop?'Upper rail stop':'Lower rail stop';}
    trayHardware.createRack(track,x,BOARD_LAYOUT);
    for(let side=0;side<2;side++){
      const group=new THREE.Group();group.position.set(x,boardHeights(0)[side],boardFaceZ(side)+BOARD_MOUNT_OFFSET);
      group.name=`Sliding chalkboard ${pair+1}${side?'B':'A'}`;scene.add(group);
      const canvas=null,ctx=null,texture=blankTexture,roughCtx=null,roughTexture=null;
      // The backing is physically recessed by .01. Avoid slope-dependent
      // depth bias, which grows at grazing angles and can occlude the chalk.
      const surface=new THREE.Mesh(new THREE.PlaneGeometry(BOARD_W,BOARD_H),new THREE.MeshPhysicalMaterial({map:texture,color:'#c9c5bb',roughness:1,roughnessMap:null,metalness:0,specularIntensity:0,envMapIntensity:0,emissive:0x000000,emissiveIntensity:0,polygonOffset:true,polygonOffsetFactor:0,polygonOffsetUnits:-1}));
      surface.name='Matte writing face';group.add(surface);
      const body=part(group,[0,0,-BOARD_LAYOUT.bodyDepth/2-.01],[BOARD_W,BOARD_H,BOARD_LAYOUT.bodyDepth],hardware.back);body.name='Solid opaque board body';
      // The opaque backing needs no decorative crossbars; preserve its perimeter frame.
      trayHardware.createFrame(group,BOARD_W,BOARD_H);
      for(const sign of [-1,1])for(const y of [-.70,.70]){
        const carriage=part(group,[sign*2.702,y,-.028],[.105,.10,.03],metal);carriage.name='Rail carriage bracket';
        const wheel=new THREE.Mesh(new THREE.CylinderGeometry(.026,.026,.030,12),hardware.rubber);
        wheel.name='Guide roller';wheel.rotation.z=Math.PI/2;wheel.position.set(sign*2.745,y,-.028);group.add(wheel);
      }
      const previousInk={value:blankTexture},inkBlend={value:1};
      surface.material.onBeforeCompile=shader=>{shader.uniforms.boardMipBias=boardMipBias;shader.uniforms.previousInk=previousInk;shader.uniforms.inkBlend=inkBlend;shader.fragmentShader='uniform float boardMipBias;\nuniform sampler2D previousInk;\nuniform float inkBlend;\n'+shader.fragmentShader.replace('#include <map_fragment>',THREE.ShaderChunk.map_fragment.replace('texture2D( map, vMapUv )','mix(texture2D(previousInk,vMapUv,boardMipBias),texture2D(map,vMapUv,boardMipBias),inkBlend)'));};
      surface.material.customProgramCacheKey=()=> 'board-readable-crossfade-120';surface.userData.boardSurface=true;
      boards.push({group,canvas,ctx,texture,roughCtx,roughTexture,previousInk,inkBlend,fadeAge:1,wet:null,last:''});
    }
    trayHardware.create(scene,x,pair);
    for(let j=0;j<trayChalkMaterials.length;j++){
      const stick=new THREE.Mesh(trayChalkGeometry,trayChalkMaterials[j]);stick.name=`Tray chalk ${pair+1} ${j+1}`;
      stick.rotation.z=Math.PI/2;stick.rotation.y=(j%2?1:-1)*.08;stick.position.set(x-.95+j*.24,TRAY.top+.020,TRAY.z+TRAY_STORAGE.center);
      stick.userData={column:pair,colorIndex:j};scene.add(stick);
    }
  }
  const countdownTargets=createCountdownTargets(THREE,boards);
  const lotteryTargets=lotteryHitTargets(THREE,boards,W,H,BOARD_W,BOARD_H);
  function voiceReport(report){const variant=report.narration?.voices?.find(v=>v.id===voiceTone);return variant?{...report,narration:{...report.narration,manifest:variant.manifest}}:report;}
  const highlighter=createBoardHighlight(THREE,{width:BOARD_W,height:BOARD_H});
  const voice=createReportVoice({finishBoard:async(page,time)=>{
    const frame=settledBoardFrame(narrationFrame(voice.manifest,time,writingPlan(pageRows.get(page),guides.get(page)),erasePlans.get(page-6)),completedWork);
    if(frame.progress>=1&&frame.phase==='hold')return false;
    const plan=writingPlan(pageRows.get(page),guides.get(page)),start=Math.max(0,frame.progress*plan.total);
    await new Promise(resolve=>boardWork={key:'write:'+page+':end',kind:'write',page,at:time,elapsed:0,duration:(plan.total-start)/plan.unitsPerSecond,start,end:plan.total,total:plan.total,resolve});return true;
  },prepareBoard:async(page,time)=>{const ready=await load(page);if(!ready)return false;const event=voice.manifest?.boards.find(b=>b.page===page);if(page>=6&&event&&time<event.writeStart&&!await load(page-6))return false;return true;}}),unbindVoiceFocus=bindVoiceFocusPause(voice);const voicePanels=Array.from({length:3},(_,column)=>{const panel=createBoardVoicePanel(THREE,scene);panel.setColumn(column);return panel;});
  let localClockDisplay=false;const timePanels=Array.from({length:3},(_,column)=>createBoardTimePanel(THREE,scene,column));
  // Three synchronized controls, centered exactly beneath their board columns.
  const consoleButtons=[],consoleTextures=[];
  const touchCanvas=document.createElement('canvas');touchCanvas.width=704;touchCanvas.height=384;
  const touchTexture=new THREE.CanvasTexture(touchCanvas);touchTexture.colorSpace=THREE.SRGBColorSpace;consoleTextures.push(touchTexture);
  for(let column=0;column<3;column++){
    const button=new THREE.Mesh(new THREE.PlaneGeometry(1.1,.65),new THREE.MeshBasicMaterial({transparent:true,opacity:0,colorWrite:false,depthWrite:false,toneMapped:false}));
    button.name=`Smart glass language touch surface ${column+1}`;button.position.set(22.4+column*5.6,-.16,-11.34);
    button.userData={action:'language',column,pressed:false,restZ:-11.34,lastLabel:'',smartGlass:true,singleToggle:true,glassPanel:0,canvas:touchCanvas,texture:touchTexture};
    const label=new THREE.Mesh(new THREE.PlaneGeometry(1.1,.60),new THREE.MeshBasicMaterial({map:touchTexture,transparent:true,opacity:1,depthWrite:false,toneMapped:false}));
    label.position.z=.008;label.userData.screenLabel=true;button.add(label);addTextSheen(THREE,button,touchTexture,1.1,.60);scene.add(button);consoleButtons.push(button);
  }
  function setConsoleState(){
    if(consoleButtons.every(button=>button.userData.lastLabel===language))return;
    const targetLanguage=language==='zh'?'en':'zh',label=targetLanguage==='zh'?'中':'EN';
    for(const button of consoleButtons){button.userData.lastLabel=language;button.userData.visibleLabel=label;button.userData.targetLanguage=targetLanguage;}
    const c=touchCanvas.getContext('2d');c.clearRect(0,0,704,384);
    c.textAlign='center';c.shadowBlur=0;
    c.font='500 '+(148*CONTROL_VISUAL_SCALE)+'px '+SCREEN_FONT;
    c.fillStyle=SCREEN_COLORS.text;c.fillText(label,352,250);
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
  const reportHeader=glassLabel(4.6,.34,reportX,3.93,'Smart glass report heading');
  reportHeader.canvas.height=76;
  addTextSheen(THREE,reportHeader.mesh,reportHeader.texture,4.6,.34);
  const programScreen=!disabled&&!navigation?.sections?createHallProgramScreen(THREE,scene,{reports,x:reportX}):null;
  if(programScreen)reportButtons.push(...programScreen.targets);
  function setReportState(){
    dateLabel=seminarDate();
    const header=reportHeader.canvas.getContext('2d');header.clearRect(0,0,1024,76);header.textAlign='right';header.fillStyle=SCREEN_COLORS.muted;header.font='400 32px '+SCREEN_MONO;
    header.fillText(dateLabel,996,52);reportHeader.mesh.userData.date=dateLabel;reportHeader.texture.needsUpdate=true;
    programScreen?.setState(hasSelection?activeReport:null,pendingReport,language,stored);
  }
  const seminarScreen=navigation?.sections?createSeminarScreen(THREE,scene,navigation):null;
  if(seminarScreen){reportHeader.mesh.visible=false;seminarScreen.setLanguage(language);}
  let autoCamera=true,cameraZoom=0;const cameraPanels=Array.from({length:3},(_,column)=>createBoardCameraControl(THREE,scene,column));
  const pageControls=Array.from({length:3},(_,column)=>createBoardPageControls(THREE,scene,column));
  const touchButtons=[...pageControls.flatMap(panel=>panel.meshes),...cameraPanels.flatMap(panel=>panel.meshes),...consoleButtons,...reportButtons,...(seminarScreen?.targets||[])];
  setConsoleState();setReportState();
  if(disabled){reportHeader.mesh.visible=false;touchButtons.forEach(b=>b.visible=false);}
  const chalk=new THREE.Mesh(new THREE.CylinderGeometry(.017,.014,.17,8),new THREE.MeshStandardMaterial({color:'#f3edda',roughness:1,metalness:0,emissive:'#e3dcc8',emissiveIntensity:.32,envMapIntensity:.15}));
  const chalkAxis=new THREE.Vector3(.22,-.42,.88).normalize();chalk.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0),chalkAxis);chalk.name='Writing chalk';scene.add(chalk);
  const eraserWidth=EW*2/W*BOARD_W,eraserHeight=EH*2/H*BOARD_H;
  const eraser=trayHardware.createEraser(eraserWidth,eraserHeight,hardware);scene.add(eraser);
  const felt=eraser.getObjectByName('Textured layered felt');
  const parkedErasers=Array.from({length:3},(_,column)=>{
    const parked=trayHardware.createParkedEraser(eraser,column);scene.add(parked);return parked;
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
  let grain,dust;
  let seed=831;const random=()=>{seed=(seed*1664525+1013904223)>>>0;return seed/4294967296;};
  // Empty classrooms retain their board meshes but allocate no full-size ink buffers.
  const wipeCanvas=document.createElement('canvas');wipeCanvas.width=1;wipeCanvas.height=1;
  const wipeCtx=wipeCanvas.getContext('2d');let wipeSamples=0;
  const erasedGrain=document.createElement('canvas');erasedGrain.width=erasedGrain.height=1;const erasedGrainCtx=erasedGrain.getContext('2d');
  function resetWipe(){wipeCanvas.width=hasSelection?W*pixelScale:1;wipeCanvas.height=hasSelection?H*pixelScale:1;wipeCtx.setTransform?.(pixelScale,0,0,pixelScale,0,0);wipeSamples=0;}
  function inkCanvas(scale=pixelScale){const c=document.createElement('canvas');c.width=W*scale;c.height=H*scale;const ctx=c.getContext('2d');ctx.setTransform?.(scale,0,0,scale,0,0);return [c,ctx];}
  function paintBackground(ctx,w,h){if(isCrystalScheme(trayHardware.tone))paintStoneBoard(ctx,w,h);else{ctx.fillStyle='#193d33';ctx.fillRect(0,0,w,h);}}
  function ensureInk(board){
    if(!grain){
      let g,d;[grain,g]=inkCanvas();paintBackground(g,W,H);
      if(!isCrystalScheme(trayHardware.tone))for(let i=0;i<12000;i++){g.fillStyle=i%2?'#e7f0d808':'#041c1b18';g.fillRect(random()*W,random()*H,1+random()*2,1);}
      [dust,d]=inkCanvas();d.fillStyle=isCrystalScheme(trayHardware.tone)?'#34363818':'#193d3328';for(let i=0;i<6000;i++)d.fillRect(random()*W,random()*H,.5+random(),.6);
    }
    if(board.canvas)return;
    [board.canvas,board.ctx]=inkCanvas();
    // A new canvas is transparent black. Seed it before binding or capturing
    // a previous frame, including when the room is still outside the camera.
    paintBackground(board.ctx,W,H);
    board.texture=new THREE.CanvasTexture(board.canvas);board.texture.colorSpace=THREE.SRGBColorSpace;
    board.texture.anisotropy=Math.min(pixelScale<1?4:16,renderer.capabilities.getMaxAnisotropy());board.texture.generateMipmaps=true;board.texture.minFilter=THREE.LinearMipmapLinearFilter;
    const roughCanvas=document.createElement('canvas');roughCanvas.width=W/4;roughCanvas.height=H/4;board.roughCtx=roughCanvas.getContext('2d');board.roughCtx.fillStyle='white';board.roughCtx.fillRect(0,0,W/4,H/4);board.roughTexture=new THREE.CanvasTexture(roughCanvas);
    const material=board.group.children[0].material;material.map=board.texture;material.roughnessMap=board.roughTexture;material.needsUpdate=true;
  }
  function beginContentFade(board){
    if(!board.canvas||contentFadeQueue.includes(board))return;
    contentFadeQueue.push(board);
    if(!board.previousCanvas){board.previousCanvas=document.createElement('canvas');board.previousCanvas.width=W;board.previousCanvas.height=H;board.previousInk.value=new THREE.CanvasTexture(board.previousCanvas);board.previousInk.value.colorSpace=THREE.SRGBColorSpace;board.previousInk.value.anisotropy=board.texture.anisotropy;}
    if(board.previousCanvas.width!==board.canvas.width||board.previousCanvas.height!==board.canvas.height){board.previousInk.value.dispose();board.previousCanvas.width=board.canvas.width;board.previousCanvas.height=board.canvas.height;board.previousInk.value=new THREE.CanvasTexture(board.previousCanvas);board.previousInk.value.colorSpace=THREE.SRGBColorSpace;board.previousInk.value.anisotropy=board.texture.anisotropy;}
    board.previousCanvas.getContext('2d').drawImage(board.canvas,0,0);
    board.previousInk.value.needsUpdate=true;board.fadeAge=0;board.inkBlend.value=0;
  }
  function draw(index,preparing=false){
    if(translating&&!preparing)return;
    const board=boards[index],slot=clock.slots[index];
    if(!preparing&&(options.isActive?.()===false||!renderActive||hydrating||stored||storageProgress>0))return;
    const content={page:slot.page,progress:slot.progress,available:cache.has(slot.page)};
    if(preparing||(pages[slot.page]?.orderedBoard&&!voice.transportPlaying)){board.fadeAge=1;board.inkBlend.value=1;}else if(boardContentJump(board.content,content))beginContentFade(board);board.content=content;
    if(slot.page<0){if(board.last==='blank')return;board.last='blank';board.paintState=null;if(board.canvas){paintBackground(board.ctx,W,H);inkUploader.upload(board);board.roughCtx.fillStyle='white';board.roughCtx.fillRect(0,0,W/4,H/4);board.roughTexture.needsUpdate=true;board.roughKey='';}return;}
    ensureInk(board);
    const rect=renderer.domElement?.getBoundingClientRect?.(),priorScale=board.canvas.width/W,ratio=renderer.getPixelRatio?.()||1;let pixelWidth=(rect?.width||W)*ratio,pixelHeight=(rect?.height||H)*ratio;
    if(index===clock.active&&options.camera){board.group.updateWorldMatrix(true,false);const points=[[-BOARD_W/2,-BOARD_H/2],[BOARD_W/2,-BOARD_H/2],[-BOARD_W/2,BOARD_H/2],[BOARD_W/2,BOARD_H/2]].map(([x,y])=>new THREE.Vector3(x,y,0).applyMatrix4(board.group.matrixWorld).project(options.camera));pixelWidth=Math.min(rect.width,Math.abs(Math.max(...points.map(p=>p.x))-Math.min(...points.map(p=>p.x)))*rect.width/2)*ratio;pixelHeight=Math.min(rect.height,Math.abs(Math.max(...points.map(p=>p.y))-Math.min(...points.map(p=>p.y)))*rect.height/2)*ratio;}
    const scale=index===clock.active&&voice.state.started&&!openingDemo?boardInkScale({base:pixelScale,previous:priorScale,width:pixelWidth,height:pixelHeight,maxTextureSize:renderer.capabilities.maxTextureSize}):priorScale;
    if(board.canvas.width!==Math.round(W*scale)){const old=board.texture;board.canvas.width=Math.round(W*scale);board.canvas.height=Math.round(H*scale);board.ctx.setTransform(scale,0,0,scale,0,0);board.texture=new THREE.CanvasTexture(board.canvas);board.texture.colorSpace=THREE.SRGBColorSpace;board.texture.anisotropy=old.anisotropy;board.texture.minFilter=old.minFilter;board.group.children[0].material.map=board.texture;board.group.children[0].material.needsUpdate=true;old.dispose();board.last=null;board.inkUploaded=false;board.paintState=null;}
    const ctx=board.ctx;
    const erasing=index===clock.active&&clock.phase==='erase'&&clock.progress>0;
    const wet=board.wet,wetAge=wet?effectTime-wet.started:Infinity;
    const wetKey=''; // A dry felt eraser leaves no dark water/roughness stamps.
    const physical=pages[slot.page]?.exerciseBoard;
    const activity=physical?null:currentExercise(slot.page);
    const activityEvent=voice.manifest?.boards.find(b=>b.page===slot.page),inlineWait=physical&&activityEvent?.waits?.find(w=>w.exercise&&voice.state.time-activityEvent.start>=w.start&&voice.state.time-activityEvent.start<w.end);const automatic=physical&&voice.state.activity?.page===slot.page?voice.state.activity:inlineWait?{page:slot.page,activityType:'exercise',remaining:inlineWait.end-(voice.state.time-activityEvent.start),duration:inlineWait.seconds}:null;
    const choice=undefined;
    const lottery=physical?studentLottery.view(activeReport.id+':'+slot.page,{auto:slot.page===clock.page&&automatic?.activityType==='exercise',animate:!erasing&&slot.page===clock.page}):null;
    const activityKey=(lottery?.key||'')+':'+(pages[slot.page].period==='break'?Math.floor(voice.state.time)+':'+voice.state.phase:automatic?Math.ceil(automatic.remaining)+':'+voice.state.phase:'');
    const key=`${omittedProofPages.size}:${activityKey}:${slot.page}:${slot.progress}:${erasing?clock.progress:''}:${cache.has(slot.page)}:${wetKey}`;
    if(!preparing&&(options.isActive?.()===false||!renderActive||hydrating||stored||storageProgress>0))return;
    if(board.last===key)return;
    const previous=board.paintState,image=omittedProofPages.has(slot.page)?null:cache.get(slot.page),rows=pageRows.get(slot.page)||pages[slot.page].rows||[],pose=rows.length?writingPose(rows,slot.progress,guides.get(slot.page)):null;let area=null;
    if(!preparing&&board.last&&previous&&previous.page===slot.page&&previous.image===image&&previous.omitted===omittedProofPages.size){
      area=changedInkRect(rows,previous.progress,slot.progress,p=>writingPose(rows,p,guides.get(slot.page)),W,H);
      if(previous.activity!==activityKey){const bottom=Math.max(200,...rows.filter(r=>r.mainLine<=pages[slot.page].questionLineCount).map(r=>r[1]+r[3]));area=unionInkRects([area,...(physical?[LOTTERY_RECT,[W/2-180,Math.min(H-150,bottom+20),360,135]]:pages[slot.page].period==='break'?[[W/2-230,295,460,125]]:[[0,0,W,H]])],W,H);}
      if(erasing&&image){const plan=wet?.plan||erasePlans.get(slot.page),samples=Math.max(700,Math.ceil(plan.total/2)),end=Math.floor(clock.progress*samples),stamps=[];for(let i=wipeSamples;i<=end;i++){const p=eraserPose(i/samples,W,H,plan);if(p.contact)stamps.push([p.x-EW-EH,p.y-EW-EH,(EW+EH)*2,(EW+EH)*2]);}area=unionInkRects([area,unionInkRects(stamps,W,H)],W,H);}
      if(!area){board.last=key;board.paintState={page:slot.page,progress:slot.progress,image,activity:activityKey,omitted:omittedProofPages.size};return;}
    }
    const rasterStarted=performance.now();board.last=key;if(area){ctx.save();ctx.beginPath();ctx.rect(...area);ctx.clip();}
    ctx.drawImage(grain,0,0,W,H);
    if(activity){const frame=drawClassroomActivity(ctx,activity,{paused:voice.state.phase==='paused',language,sheetIndex:choice});exerciseFrames.set(slot.page,frame);const eraseKey=activity.start+':'+activity.feedback+':'+frame.sheetIndex;if(exerciseEraseKeys.get(slot.page)!==eraseKey){erasePlans.set(slot.page,erasingPlan(null,frame.eraseRows));exerciseEraseKeys.set(slot.page,eraseKey);}}
    else if(image){
      // Reveal each complete mathematical row left to right, preserving exact
      // SVG fractions/superscripts. The grain is deterministic, never flickering.
      rows.forEach(([x,y,w,h],row)=>{
        if(area&&!intersectsInk(rows[row].strokeRaster?.glyphRect||rows[row],area))return;
        if(rows[row].strokeRaster){paintChineseGroup(ctx,rows,row,i=>rasterStrokeReveal(rows,slot.progress,i,guides.get(slot.page),pose));return;}
        if(rows[row].strokePath){paintChalkStroke(ctx,strokeReveal(rows,slot.progress,row,guides.get(slot.page),pose),rows[row].chalkColor,rows[row].strokeWidth);return;}
        const width=inkReveal(rows,slot.progress,row,guides.get(slot.page),pose);
        if(width>0){ctx.save();ctx.beginPath();ctx.rect(x,y,width,h);ctx.clip();ctx.drawImage(image,0,0);ctx.restore();}
      });
      if(language!=='zh')ctx.drawImage(dust,0,0,W,H);
    }
      if(lottery&&image)drawStudentLottery(ctx,lottery,language);
      if(erasing&&image){
        const wipePlan=wet?.plan||erasePlans.get(slot.page),samples=Math.max(700,Math.ceil(wipePlan.total/2)),end=Math.floor(clock.progress*samples);
        for(let i=wipeSamples;i<=end;i++){
          const p=eraserPose(i/samples,W,H,wipePlan);if(!p.contact)continue;
          stampFelt(wipeCtx,p);
        }
        wipeSamples=end+1;
        if(erasedGrain.width!==grain.width||erasedGrain.height!==grain.height){erasedGrain.width=grain.width;erasedGrain.height=grain.height;}
        erasedGrainCtx.globalCompositeOperation='source-over';erasedGrainCtx.clearRect(0,0,erasedGrain.width,erasedGrain.height);erasedGrainCtx.drawImage(grain,0,0);erasedGrainCtx.globalCompositeOperation='destination-in';erasedGrainCtx.drawImage(wipeCanvas,0,0);ctx.drawImage(erasedGrain,0,0,W,H);
      }
    if(omittedProofPages.size&&slot.page===pages.length-1){ctx.save();ctx.font='32px '+SCREEN_FONT;ctx.fillStyle='#9bc9df';ctx.textAlign='center';ctx.fillText(language==='zh'?'第三定理证明略过；下一课使用其结论。':'The third proof was omitted; its conclusions are used in the next class.',W/2,475,1390);ctx.restore();}
    if(image&&pages[slot.page].period!=='break')drawClassroomMetadata(ctx,pages[slot.page],slot.page,language,{exercise:physical||Boolean(activity),total:pages.length});
    if(image&&pages[slot.page].period==='break'){const b=voice.manifest?.boards.find(b=>b.page===slot.page),remaining=Math.min(300,Math.max(0,Math.ceil((b?.end??300)-(b?voice.state.time:0)))),label=Math.floor(remaining/60)+':'+String(remaining%60).padStart(2,'0');ctx.save();ctx.font='86px '+SCREEN_MONO;ctx.textAlign='center';ctx.fillStyle='#eee9d5';ctx.fillText(label,W/2,390);ctx.restore();}
    if(physical&&slot.page===clock.page){const b=voice.manifest?.boards.find(b=>b.page===slot.page),a=voice.manifest?.chapters.find(c=>c.page===slot.page&&c.activityType==='exercise'),ownWait=b?.waits?.find(w=>w.exercise&&voice.state.time-b.start>=w.start&&voice.state.time-b.start<w.end),thinking=!!ownWait||(voice.state.activity?.activityType==='exercise'&&voice.state.activity.page===slot.page);let text='',countdownRect=null;if(thinking){const seconds=Math.max(0,Math.ceil((ownWait?ownWait.end-(voice.state.time-b.start):voice.state.activity.remaining)-1e-6));text=Math.floor(seconds/60)+':'+String(seconds%60).padStart(2,'0');const questionBottom=Math.max(200,...(pageRows.get(slot.page)||[]).filter(r=>r.mainLine<=pages[slot.page].questionLineCount).map(r=>r[1]+r[3])),y=Math.min(H-70,questionBottom+110);ctx.save();ctx.font='76px '+SCREEN_MONO;ctx.textAlign='center';ctx.fillStyle=voice.state.phase==='paused'?'#c8d9d9':'#d4edf0';ctx.fillText(text,W/2,y);countdownRect=countdownTextRect(ctx,text,W/2,y,82);ctx.restore();}exerciseFrames.set(slot.page,{physical:true,page:slot.page,lines:pages[slot.page].exerciseLines.length+1,feedback:!!a&&voice.state.time>=a.start+a.duration,thinkingSeconds:b?.waits?.find(w=>w.exercise)?.seconds??a?.duration,countdown:text,countdownCentered:true,countdownRect});}


    const r=board.roughCtx,roughChanged=board.roughKey!==wetKey;
    if(roughChanged){r.fillStyle='white';r.fillRect(0,0,W/4,H/4);}
    if(roughChanged){board.roughKey=wetKey;board.roughTexture.needsUpdate=true;}
    if(area)ctx.restore();lastRasterMs=performance.now()-rasterStarted;inkUploader.upload(board,area);board.paintState={page:slot.page,progress:slot.progress,image,activity:activityKey,omitted:omittedProofPages.size};
  }
  function positionTool(tool,x,y){
    const board=boards[clock.active].group;
    tool.position.set(board.position.x+(x/W-.5)*BOARD_W,board.position.y+(.5-y/H)*BOARD_H,board.position.z+.014);
  }
  function select(page){if(disabled)return;if(voice.manifest)return seek(page,{preservePlayback:true});openingDemo=null;clock.select(page);targets[Math.floor(clock.active/2)]=clock.active%2;version++;load(clock.page).catch(error=>{loadingError=error;});}
  async function seek(page,{preservePlayback=false}={}){
    if(disabled)return false;
    cancelBoardWork();boardPreparation=null;
    openingDemo=null;
    const request=++seekRequest,epoch=generation;
    const target=Math.max(clock.startAt,Math.min(clock.stopAt,Math.trunc(page)||0));
    const board=voice.manifest?.boards.find(b=>b.page===target);
    loadingError=null;assetRetry.clear(target);requestedPage=target;
    seeking=true;seekPinned=new Set(Array.from({length:target-Math.max(clock.startAt,target-(voice.manifest?6:5))+1},(_,i)=>Math.max(clock.startAt,target-(voice.manifest?6:5))+i));
    try{
      const history=[...seekPinned].filter(i=>i!==target),preparation=load(target);
      // Only the destination is mandatory. An unavailable old page cannot block it.
      void preparation.then(async()=>{for(const page of history){if(epoch!==generation||request!==seekRequest)return;try{await load(page);}catch{}}}).catch(()=>{});
      const commit=preparation.then(()=>{
      if(request!==seekRequest||epoch!==generation)return false;
      clock.seek(target);
      if(board)syncNarrationClock(clock,narrationFrame(voice.manifest,board.writeStart,writingPlan(pageRows.get(target),guides.get(target)),erasePlans.get(target-6)),boardSlot);
      for(let pair=0;pair<3;pair++){
        const a=clock.slots[pair*2].page,b=clock.slots[pair*2+1].page;
        mix[pair]=targets[pair]=b>a?1:0;
        boardHeights(mix[pair]).forEach((height,side)=>boards[pair*2+side].group.position.y=height);
      }
      eraserReturn=null;eraserPickup=null;eraser.visible=false;eraser.userData.state='resting';
      parkedErasers.forEach(e=>e.visible=true);chalk.visible=false;previousTip=null;
      particles.forEach(p=>p.life=0);particlePositions.fill(-10000);dustGeometry.attributes.position.needsUpdate=true;
      boards.forEach(b=>{b.wet=null;b.last='';});resetWipe();
      boards.forEach((_,i)=>draw(i,true));version++;
      loadingError=null;return true;
      });
      if(board){lessonBudget.configure(voice.manifest);lessonBudget.seek(board.writeStart,voice.manifest.boards.filter(b=>b.optionalProof));omittedProofPages.clear();
        // Audio still waits for ink before resuming. Board navigation must not
        // wait for the entire MP3; the destination and controls can be ready first.
        void voice.seek(board.writeStart,{preservePlayback,ready:commit}).catch(()=>{});
      }else{voice.pause();if(activeReport.narration&&voiceEnabled)void voice.manifestReady.then(manifest=>{if(request!==seekRequest||epoch!==generation)return;const destination=manifest?.boards.find(b=>b.page===target);if(destination)void voice.seek(destination.writeStart,{preservePlayback:false,ready:commit}).catch(()=>{});});}
      return await commit;
    }catch(error){if(request===seekRequest)loadingError=error;throw error;}
    finally{if(request===seekRequest){seeking=false;requestedPage=null;seekPinned.clear();}}
  }
  async function revealCurrent(){
    if(disabled||!hasSelection||seeking)return false;
    const page=clock.page,epoch=generation,request=seekRequest;voice.pause();playing=false;await load(page);if(epoch!==generation||request!==seekRequest||page!==clock.page||seeking)return false;
    const event=voice.manifest?.boards.find(b=>b.page===page);
    if(event&&!await voice.seek(Math.max(event.writeStart,event.end-.03)))return false;
    if(epoch!==generation||request!==seekRequest||page!==clock.page||seeking)return false;
    workManifest=voice.manifest;revealedPages.add(page);completedWork.add('write:'+page+':end');boardReview.mark(page);
    if(boardWork?.page===page){boardWork.resolve();boardWork=null;}
    const frame={page,phase:'hold',progress:1,writing:false,ended:false,duration:MIN_BOARD_REVIEW_SECONDS};syncNarrationClock(clock,frame,boardSlot);
    mix[Math.floor(clock.active/2)]=targets[Math.floor(clock.active/2)]=clock.active%2;
    boardHeights(mix[Math.floor(clock.active/2)]).forEach((h,s)=>boards[Math.floor(clock.active/2)*2+s].group.position.y=h);
    chalk.visible=false;eraser.visible=false;eraserPickup=null;eraserReturn=null;eraser.userData.state='resting';boards.forEach(b=>{b.last='';b.wet=null;});resetWipe();boards.forEach((_,i)=>draw(i,true));version++;return true;
  }
  function finishOpening(){
    openingDemo=null;if(!storageRig)return;
    voice.pause();stored=true;playing=false;chalk.visible=false;eraser.visible=false;fallingDust.visible=false;
    consoleButtons.forEach(b=>b.visible=false);updateStorageLabel();setReportState();
    if(screenHub?.state.power)screenHub.action('screen:power');
  }
  function update(dt,reduced=false){
    if(disabled)return;
    void voice.setContextActive(present&&renderActive&&!hydrating&&!pendingReport&&!stored&&storageMotion.ready&&storageProgress===0&&options.isActive?.()!==false);
    if(options.isActive?.()===false){highlighter.hide();highlightState=null;return;}
    voice.update();
    // Move the same small control with the active physical board.
    const controlState=(pendingReport||activeReport).narration&&voiceEnabled&&!openingDemo?voice.state:{...voice.state,phase:hasSelection?(playing?'playing':'paused'):'idle',synthetic:false};
    for(const panel of voicePanels)panel.update(controlState,dt,renderActive&&!stored&&storageProgress===0&&(!screenHub||screenHub.state.power&&screenHub.state.mode==='report'));
    timePanels.forEach(panel=>panel.update(voiceEnabled&&voice.manifest?voice.state:null,clock,renderActive&&hasSelection&&!stored&&storageProgress===0&&(!screenHub||screenHub.state.power&&screenHub.state.mode==='report'),localClockDisplay));
    // Only the head of the queue advances: one board completes before the next starts.
    if(reduced||renderActive&&!hydrating&&(!voice.state.started||voice.transportPlaying))advanceBoardQueue(contentFadeQueue,dt,reduced);
    screenHub?.update(dt,storageProgress,reduced);
    const withVoice=hasSelection||Boolean(pendingReport);
    for(const button of consoleButtons){const position=reportControlLayout(button.userData.column,withVoice).language;placeTrayControl(button,position);button.visible=renderActive&&!hydrating&&!stored&&storageMotion.ready&&storageProgress===0&&(!screenHub||screenHub.state.power&&screenHub.state.mode==='report');}
    pageControls.forEach(panel=>panel.update({previousEnabled:hasSelection&&clock.page>clock.startAt,nextEnabled:hasSelection&&clock.page<clock.stopAt,activity:voice.state.activity,visible:renderActive&&!hydrating&&hasSelection&&!stored&&storageMotion.ready&&storageProgress===0&&(!screenHub||screenHub.state.power&&screenHub.state.mode==='report')}));
    for(const target of lotteryTargets){const page=clock.slots[target.userData.index].page;target.visible=hasSelection&&page>=0&&pages[page]?.exerciseBoard&&target.userData.index===clock.active&&clock.phase!=='erase'&&renderActive&&!stored;}
    cameraPanels.forEach(panel=>panel.update(autoCamera,renderActive&&!hydrating&&hasSelection&&!stored&&storageMotion.ready&&storageProgress===0&&(!screenHub||screenHub.state.power&&screenHub.state.mode==='report'),withVoice,cameraZoom));
    voicePanels.forEach(panel=>updateTextSheen(THREE,panel.mesh,dt,reduced));timePanels.forEach(panel=>updateTextSheen(THREE,panel.mesh,dt,reduced));
    if(storageRig){
      storageMotion.update(dt,stored);storageProgress=storageMotion.progress;
      const t=storageProgress*storageProgress*(3-2*storageProgress);
      storageRig.position.y=t===0?0:-7.2*t;storageRig.visible=storageProgress<1;
      const u=storageMotion.lid,k=u*u*(3-2*u);
      if(storageCap)storageCap.visible=u===0;
      for(const lid of storageLids){lid.visible=u>0;lid.position.z=lid.userData.closedZ+lid.userData.sign*.55*k;lid.position.y=lid.userData.closedY-.065*Math.min(1,u*5);}
      consoleButtons.forEach(b=>b.visible=!stored&&storageMotion.ready&&storageProgress===0&&(!screenHub||screenHub.state.power&&screenHub.state.mode==='report'));
      updateStorageLabel(reduced);if(storageProgress>0||stored||!storageMotion.ready){highlighter.hide();highlightState=null;return;}
    }
    // Offscreen boards retain their exact state; looking at sunrise must not fast-forward pages.
    if(!renderActive||hydrating||translating||seeking){highlighter.hide();highlightState=null;return;}
    dt=Math.max(0,Math.min(.1,dt));for(const b of touchButtons){updateTextSheen(THREE,b,dt,reduced);}updateTextSheen(THREE,reportHeader.mesh,dt,reduced);
    dateCheck+=dt;if(dateCheck>=1){dateCheck=0;if(seminarDate()!==dateLabel)setReportState();}if(playing&&!reduced)effectTime+=dt;
    const oldPhase=clock.phase,oldActive=clock.active;
    const narrated=voice.manifest&&voice.state.started;let narrationWriting=true;
    if(narrated){
      if(workManifest!==voice.manifest){cancelBoardWork();workManifest=voice.manifest;}
      if(boardWork&&!voice.boardHeld)cancelBoardWork();
      lessonBudget.configure(voice.manifest);lessonBudget.advance(dt,{...voice.state,transportPlaying:voice.transportPlaying});
      let frame=narrationFrame(voice.manifest,voice.state.time);
      const priorPage=previousNarrationTime===null?frame.page:voice.manifest.boards.findLast(b=>b.start<=previousNarrationTime)?.page??frame.page;
      const needed=[frame.page,frame.phase==='erase'&&frame.page>=6?frame.page-6:-1].filter(i=>i>=0);
      if(needed.every(i=>cache.has(i))&&!seeking){
        frame=settledBoardFrame(narrationFrame(voice.manifest,voice.state.time,writingPlan(pageRows.get(frame.page),guides.get(frame.page)),erasePlans.get(frame.page-6)),completedWork);
        if(translatedInk){if(frame.page!==translatedInk.page)translatedInk=null;else if(frame.phase==='write'||frame.phase==='hold'){const natural=frame.progress;if(natural<translatedInk.progress)frame={...frame,progress:translatedInk.progress,phase:translatedInk.progress===1?'hold':frame.phase,writing:false};else if(voice.transportPlaying)translatedInk=null;}}
        if(revealedPages.has(frame.page))frame={...frame,phase:'hold',progress:1,writing:false};
        if(frame.phase==='hold'&&frame.progress===1)boardReview.mark(frame.page);
        if(frame.phase==='erase'&&eraseRun?.page!==frame.page){const event=voice.manifest.boards.find(b=>b.page===frame.page),plan=erasePlans.get(frame.page-6);eraseRun={page:frame.page,duration:plan.duration,elapsed:previousNarrationTime===null?Math.max(0,Math.min(plan.duration,voice.state.time-event.eraseStart-1.8)):0};}
        if(eraseRun?.page===frame.page){
          if(voice.transportPlaying&&eraser.userData.state==='erasing')eraseRun.elapsed=Math.min(eraseRun.duration,eraseRun.elapsed+dt);
          if(eraseRun.elapsed>=eraseRun.duration&&eraser.userData.state==='resting')completedWork.add('erase:'+eraseRun.page);
          if(frame.phase==='erase')frame={...frame,progress:eraseRun.elapsed/eraseRun.duration,duration:eraseRun.duration};
        }
        if(!boardWork&&voice.state.phase==='playing'&&pageRows.has(priorPage)){
          const work=narrationWork(voice.manifest,voice.state.time,previousNarrationTime,writingPlan(pageRows.get(priorPage),guides.get(priorPage)),erasePlans.get(priorPage-6),completedWork,boardReview.remaining(priorPage));
          if(work){if(work.kind==='review')boardReview.mark(work.page);if(work.kind==='erase'){if(eraseRun?.page!==work.page)eraseRun={page:work.page,duration:work.duration,elapsed:work.elapsed};work.elapsed=eraseRun.elapsed;}const job=new Promise(resolve=>boardWork={...work,resolve});void voice.holdForBoard(job,work.at);}
        }
        if(boardWork){
          if(boardWork.kind==='erase')boardWork.elapsed=eraseRun.elapsed;
          else if(boardWork.kind==='review')boardWork.elapsed=boardWork.duration-boardReview.remaining(boardWork.page);
          else if(voice.transportPlaying)boardWork.elapsed+=dt*writingSpeed;
          frame=boardWorkFrame(boardWork);
          if(boardWork.elapsed>=boardWork.duration&&(boardWork.kind!=='erase'||eraser.userData.state==='resting')){if(boardWork.kind==='write'&&boardWork.end>=boardWork.total)boardReview.mark(boardWork.page);completedWork.add(boardWork.key);boardWork.resolve();boardWork=null;}
        }
        if(voice.state.phase==='playing'||voice.boardHeld)previousNarrationTime=voice.state.time;
        if(!boardWork&&!proofJumping&&voice.transportPlaying&&lessonBudget.shouldSkip(frame,voice.manifest.boards.filter(b=>b.optionalProof))){void omitOptionalProof().catch(error=>{loadingError=error;});return;}
        narrationWriting=frame.writing;syncNarrationClock(clock,frame,boardSlot);targets[Math.floor(clock.active/2)]=clock.active%2;
        playing=voice.transportPlaying;
        if(!cache.has(Math.min(frame.page+1,pages.length-1)))load(Math.min(frame.page+1,pages.length-1),undefined,{background:true}).catch(()=>{});
        const stamp=performance.now();if(stamp-lookaheadAt>500&&!pending.size&&(!voice.transportPlaying||!frame.writing)){lookaheadAt=stamp;const next=[clock.page+2,clock.page+3].find(p=>p<pages.length&&!cache.has(p));if(next!==undefined)void load(next,undefined,{background:true}).catch(()=>{});}
      }else{
        playing=false;
        if(!loadingError&&!boardPreparation){
          const epoch=generation,request=seekRequest,preparing=Promise.all(needed.map(i=>load(i)));boardPreparation=preparing;
          const observed=preparing.catch(error=>{if(epoch===generation&&request===seekRequest){loadingError=error;voice.failForBoard(error);}throw error;}).finally(()=>{if(boardPreparation===preparing)boardPreparation=null;});
          if(voice.state.phase==='playing')void voice.suspendUntil(observed);else observed.catch(()=>{});
        }
      }
    }else if(boardWork||workManifest)cancelBoardWork();
    const ready=cache.has(clock.page)&&(clock.slots[clock.active].page<0||cache.has(clock.slots[clock.active].page));
    if(!narrated&&clock.phase==='hold'){boardReview.mark(clock.page);clock.elapsed=Math.max(clock.elapsed,Math.min(clock.duration,MIN_BOARD_REVIEW_SECONDS-boardReview.remaining(clock.page)));}
    if(!ready&&!loadingError){load(clock.page).catch(error=>{loadingError=error;});load(clock.slots[clock.active].page).catch(error=>{loadingError=error;});}
    // Ordinary reports retain their original mechanism. Narration uses Audio.currentTime.
    const collectingEraser=clock.phase==='erase'&&eraser.userData.state!=='erasing'||clock.phase==='write'&&Boolean(eraserReturn);
    if(present&&!narrated&&(!activeReport.narration||!voiceEnabled||openingDemo?.phase==='writing')&&playing&&hasSelection&&ready&&!seeking&&!loadingError&&!reduced&&!collectingEraser){
      const prior=clock.page;clock.update(dt*(clock.phase==='write'?writingSpeed:1));
      if(prior!==clock.page){targets[Math.floor(clock.active/2)]=clock.active%2;load(clock.page).catch(error=>{loadingError=error;});}
    }
    if(openingDemo?.phase==='writing'&&playing&&ready&&!seeking&&!loadingError&&(oldPhase==='write'||reduced))openingDemo.elapsed+=dt;
    if(clock.phase==='erase'){
      if(oldPhase!=='erase'||oldActive!==clock.active||!boards[clock.active].wet){boards[clock.active].wet={started:effectTime,progress:0,duration:clock.duration,plan:erasePlans.get(clock.slots[clock.active].page)};resetWipe();}
      boards[clock.active].wet.progress=clock.progress;
    }else if(oldPhase==='erase'&&boards[oldActive].wet)boards[oldActive].wet.progress=1;
    if(reduced)for(const board of boards)board.wet=null;
    for(let pair=0;pair<3;pair++){
      if(!narrated||voice.transportPlaying||seeking)mix[pair]=reduced?targets[pair]:THREE.MathUtils.damp(mix[pair],targets[pair],3*.7,dt);
      boardHeights(mix[pair]).forEach((height,side)=>boards[pair*2+side].group.position.y=height);
    }
    chalk.visible=present&&playing&&!reduced&&ready&&clock.phase==='write'&&!eraserReturn&&(!narrated||narrationWriting);
    const erasing=!reduced&&ready&&clock.phase==='erase'&&clock.progress<1;
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
        const t=Math.min(1,eraserPickup.elapsed/1.8);
        const p=eraserPose(clock.progress,W,H,boards[clock.active].wet?.plan);
        positionTool(eraserContact,p.x,p.y);eraserContact.position.z+=.052+p.lift;eraserContact.rotation.set(.03,0,-p.angle);
        const pose=eraserTransfer(eraserContact.position,eraserPickup.position,1-t,TRAY.z+TRAY.depth/2+.22);
        eraser.position.set(pose.x,pose.y,pose.z);
        eraser.quaternion.slerpQuaternions(eraserContact.quaternion,eraserPickup.quaternion,pose.rotation);
        eraser.userData.state='pickup';
        if(t===1){eraserPickup=null;eraser.userData.state='erasing';boards[clock.active].wet.started=effectTime;}
      }else eraser.userData.state='erasing';
    }else if(eraserReturn){
      if(playing)eraserReturn.elapsed+=dt;
      const t=Math.min(1,eraserReturn.elapsed/1.8),rest=parkedErasers[eraserReturn.column];
      const pose=eraserTransfer(eraserReturn.position,rest.position,t,TRAY.z+TRAY.depth/2+.22);
      eraser.position.set(pose.x,pose.y,pose.z);
      eraser.quaternion.slerpQuaternions(eraserReturn.quaternion,rest.quaternion,pose.rotation);
      eraser.visible=t<1;eraser.userData.state=t<1?'returning':'resting';if(t===1)eraserReturn=null;
    }else{eraser.visible=false;eraser.userData.state='resting';}
    parkedErasers.forEach((rest,column)=>{rest.visible=!(eraser.visible&&column===eraserColumn);});
    if(chalk.visible){
      if(lastWritePage!==clock.page){lastWritePage=clock.page;previousTip=null;if(chalkLength(wear)<.06)wear=0;}
      const pose=writingPose(pageRows.get(clock.page)||pages[clock.page].rows,clock.progress,guides.get(clock.page));positionTool(chalk,pose.x,pose.y);chalk.position.z+=pose.toolLift??(pose.contact?0:.055+pose.lift);
      const ink=pageRows.get(clock.page)?.[pose.row]?.chalkColor||'#f3edda';chalk.material.color.set(ink);chalk.material.emissive.set(ink);chalk.userData.inkColor=ink;
      const tip=chalk.position.clone();
      if(previousTip&&pose.contact)wear+=Math.min(.07,tip.distanceTo(previousTip))*.007;
      const length=chalkLength(wear),propScale=1/(scene.scale.y||1);chalk.scale.set(propScale,length/.17*propScale,propScale);chalk.position.addScaledVector(chalkAxis,length*propScale/2);chalk.userData.length=length;chalk.userData.contact=pose.contact;previousTip=tip;
      dustAccumulator+=dt;
      if(language!=='zh'&&pose.contact&&dustAccumulator>.09){dustAccumulator=0;const i=particleCursor++%particleCount;particles[i]={life:1.1,vx:(random()-.5)*.025,vy:-.015};particlePositions.set([tip.x,tip.y,tip.z+.016],i*3);}
    }else previousTip=null;
    if(erasing&&!eraserPickup){const p=eraserPose(clock.progress,W,H,boards[clock.active].wet?.plan);positionTool(eraser,p.x,p.y);eraser.position.z+=.052+p.lift;eraser.rotation.set(.03,0,-p.angle);}
    fallingDust.visible=!reduced&&language!=='zh';
    if(playing&&!reduced)for(let i=0;i<particleCount;i++){
      const p=particles[i];if(p.life<=0)continue;p.life-=dt;p.vy-=dt*.11;
      particlePositions[i*3]+=p.vx*dt;particlePositions[i*3+1]+=p.vy*dt;
      if(p.life<=0)particlePositions[i*3+1]=-10000;
    }
    dustGeometry.attributes.position.needsUpdate=playing&&!reduced;
    accumulator+=dt;
    if(accumulator>=(pixelScale<1?.083:.05)||version){boards.forEach((_,i)=>draw(i));accumulator=0;version=0;}
    if(highlightManifest!==voice.manifest){highlightManifest=voice.manifest;highlightSpecs=narrationHighlights(voice.manifest);measuredHighlights.clear();}
    const rows=pageRows.get(clock.page),measured=measuredHighlights.get(clock.page);
    if(rows&&measured?.rows!==rows){const plan=writingPlan(rows,guides.get(clock.page));measuredHighlights.set(clock.page,{rows,cues:highlightSpecs.filter(c=>c.page===clock.page).map(c=>measuredHighlight(c,rows,plan)).filter(Boolean).sort((a,b)=>a.begin-b.begin)});}
    highlightState=highlightFrame(measuredHighlights.get(clock.page)?.cues||[],voice.state.time,{page:clock.page,enabled:highlightEnabled&&voiceEnabled&&voice.state.started,visible:present&&renderActive&&!seeking&&['playing','paused','away'].includes(voice.state.phase)&&(!screenHub||screenHub.state.power&&screenHub.state.mode==='report')});
    highlightState=highlighter.update(highlightState,boards[clock.active].group,dt,reduced);
    const countdownWait=classroomWaitAt(voice.manifest,voice.state.time,clock.page),countdownRect=exerciseFrames.get(clock.page)?.countdownRect;
    for(const target of countdownTargets){target.visible=!!(voice.state.started&&countdownWait&&countdownRect&&clock.slots[target.userData.index]?.page===clock.page&&renderActive&&!stored&&storageProgress===0&&!hydrating&&(!screenHub||screenHub.state.power&&screenHub.state.mode==='report'));if(target.visible){placeCountdownTarget(target,countdownRect,W,H,BOARD_W,BOARD_H);target.userData.label=language==='en'?'Skip remaining thinking time':'点击跳过剩余思考';}}
    if(openingDemo?.phase==='writing'&&openingDemo.elapsed>=5-1e-8)finishOpening();
  }
  // Reduced-motion users get complete static pages and explicit page controls.
  function staticPage(){if(disabled)return;voice.pause();clock.startWrite();clock.slots[clock.active].progress=1;clock.phase='hold';clock.elapsed=0;clock.ended=clock.page===clock.stopAt;version++;}
  boards.forEach((_,i)=>draw(i));
  // Keep the hardware and last completed texture visible at every distance.
  // Only the board carriers and tools have changing local transforms.
  function updateStorageLabel(reduced=false){if(!storageLabel)return;const step=reduced?(stored?60:0):Math.round(storageProgress*60),key=stored+':'+step;if(key===storageLabelText)return;storageLabelText=key;const c=storageLabel.canvas.getContext('2d');c.clearRect(0,0,256,256);drawPulley(c,128,128,205,step/60,stored);storageLabel.mesh.userData.label=stored?'升起黑板':'收起黑板';storageLabel.texture.needsUpdate=true;}
  if(options.retractable){
    storageRig=new THREE.Group();storageRig.name='Whole six-board retracting assembly';scene.add(storageRig);
    for(const node of [...scene.children])if(/^(Double-channel lift track|Sliding chalkboard|Wide nanmu chalk tray|Tray chalk|Tray eraser|Writing chalk|Moving blackboard eraser|Falling chalk powder)/.test(node.name))storageRig.add(node);
    const slot=storageWell=new THREE.Group();slot.name='Recessed blackboard storage shaft with sliding floor lids';scene.add(slot);
    const {left,right,back,front}=BOARD_SHAFT,width=right-left,depth=front-back,cx=(left+right)/2,cz=(back+front)/2;
    const floorY=(.028*BUILDING_SCALE-LECTURE_LIFT)/LECTURE_SCALE;
    const dark=new THREE.MeshStandardMaterial({color:'#302f2b',roughness:1});
    const floorMaterial=options.floorMaterial||new THREE.MeshStandardMaterial({color:'#9d8d79',roughness:1});
    const bottom=-9.1;
    part(slot,[cx,bottom,cz],[width,.08,depth],dark);
    for(const z of [back-.025,front+.025])part(slot,[cx,(floorY-.075+bottom)/2,z],[width+.1,floorY-.075-bottom,.05],dark);
    for(const x of [left-.025,right+.025])part(slot,[x,(floorY-.075+bottom)/2,cz],[.05,floorY-.075-bottom,depth],dark);
    for(const sign of [-1,1]){
      const lid=part(slot,[cx,floorY-.025,cz+sign*depth/4],[width,.05,depth/2],floorMaterial);
      lid.name='Flush carpet sliding shaft lid '+sign;lid.receiveShadow=true;lid.castShadow=true;
      lid.userData={closedZ:lid.position.z,closedY:lid.position.y,sign};storageLids.push(lid);
    }
    storageCap=part(slot,[cx,floorY-.025,cz],[width,.05,depth],floorMaterial);storageCap.name='Seamless closed shaft floor';storageCap.receiveShadow=true;storageLids.forEach(lid=>lid.visible=false);
    storageLabel=glassLabel(.45,.45,35.7,-1.0,'Whole blackboard storage control');
    storageLabel.canvas.width=storageLabel.canvas.height=256;storageLabel.mesh.userData.action='lectern:stow';storageLabel.mesh.userData.smartGlass=true;touchButtons.push(storageLabel.mesh);updateStorageLabel();
  }
  if(storageRig&&stored){storageRig.position.y=-7.2;storageRig.visible=false;consoleButtons.forEach(b=>b.visible=false);chalk.visible=false;eraser.visible=false;fallingDust.visible=false;}
  if(options.retractable)screenHub=createSmartGlassHub(THREE,scene,{reports:[reportHeader.mesh,...(programScreen?[programScreen.group]:reportButtons)],storage:storageLabel?.mesh,onStore:()=>{
    voice.pause();stored=true;playing=false;chalk.visible=false;eraser.visible=false;fallingDust.visible=false;consoleButtons.forEach(b=>b.visible=false);updateStorageLabel();setReportState();
  }});
  const movingNodes=new Set([scene,storageRig,...storageLids,...boards.map(b=>b.group),chalk,eraser]);
  scene.traverse(object=>{if(!movingNodes.has(object)){object.updateMatrix();object.matrixAutoUpdate=false;}});
  return {
    get cameraZoom(){return cameraZoom;},adjustCameraZoom(direction){cameraZoom=stepBoardCameraZoom(cameraZoom,direction);return cameraZoom;},
    cameraView(aspect,fov=57){const frame=boardCameraFrame(aspect,fov,cameraZoom,{column:Math.floor(clock.active/2),boardY:BOARD_LAYOUT.low,boardZ:-10.29+BOARD_MOUNT_OFFSET,frameMargin:isCrystalScheme(trayHardware.tone)?.028+.003*Math.SQRT2:.04+.0025*Math.SQRT2});return{...frame,target:scene.localToWorld(new THREE.Vector3(frame.x,frame.y,frame.z)),position:scene.localToWorld(new THREE.Vector3(frame.x,frame.y,frame.z+frame.distance))};},
    get autoCamera(){return autoCamera;},set autoCamera(value){autoCamera=Boolean(value);},
    get followEnabled(){return autoCamera&&!disabled&&hasSelection&&!stored&&storageMotion.ready&&storageProgress===0&&(!screenHub||screenHub.state.power&&screenHub.state.mode==='report');},
    get storageProgress(){return storageProgress;},get retractable(){return Boolean(storageRig);},get stored(){return stored;},
    async prepareOpening(onProgress=()=>{}){
      if(disabled||!storageRig)return false;
      const preparation=[],prepareAt=performance.now();
      playing=false;
      const openingDefault=reports.find(report=>report.id===(options.defaultReport||'ye'))||reports[0];
      if(activeReport.id!==openingDefault.id&&!await this.setReport(openingDefault.id,{loadVoice:false}))return false;
      // Prepare ink without requesting audio. Narrated openings start from the cover;
      // their first audio chapter is requested only after the arrival animation.
      await voice.select(null);
      playing=false;hasSelection=true;clock.startAt=0;clock.stopAt=pages.length-1;
      const narrated=Boolean(activeReport.narration&&voiceEnabled);
      const page=narrated?0:Math.min(7,pages.length-1);
      if(narrated){
        const loadAt=performance.now();await load(0);preparation.push({stage:'首屏字形与内容',durationMs:Math.round(performance.now()-loadAt)});clock.slots=Array.from({length:6},()=>({page:-1,progress:0}));
        clock.select(0);clock.startWrite();targets.fill(0);mix.fill(0);onProgress(.9);
      }else{
        // Reports without audio retain the short writing demonstration.
        const first=Math.max(0,page-6),count=page-first+1;let prepared=0;
        await Promise.all(Array.from({length:count},(_,i)=>load(first+i).then(()=>onProgress(++prepared/count*.9))));
        if(!await seek(Math.max(0,page-1)))return false;
        await load(page);clock.slots[boardSlot(page)]={page:-1,progress:0};
      }
      openingDemo={phase:'waiting',page,narrated,elapsed:0};
      options.onOpening?.({stage:'prepared',report:activeReport.id,kind:activeReport.kind,narrated});
      stored=false;storageMotion.reset();storageProgress=0;storageRig.position.y=0;storageRig.visible=true;
      storageLids.forEach(lid=>lid.visible=false);if(storageCap)storageCap.visible=true;
      screenHub?.report();screenHub?.update(0,0);updateStorageLabel();setReportState();
      advanceBoardQueue(contentFadeQueue,0,true);boards.forEach(b=>b.last='');
      // Allocate and upload every board before camera movement, including the
      // clean board used by the opening writing demonstration.
      for(let i=0;i<boards.length;i++){
        const canvasAt=performance.now();
        ensureInk(boards[i]);draw(i,true);
        const uploadAt=performance.now();
        renderer.initTexture?.(boards[i].texture);renderer.initTexture?.(boards[i].roughTexture);
        const uploadedAt=performance.now();
        onProgress(.9+.1*(i+1)/boards.length);
        await new Promise(resolve=>setTimeout(resolve,16));
        preparation.push({stage:'黑板 '+(i+1),canvasMs:Math.round(uploadAt-canvasAt),uploadCallMs:Math.round(uploadedAt-uploadAt),yieldMs:Math.round(performance.now()-uploadedAt),width:boards[i].canvas.width,height:boards[i].canvas.height});
      }
      options.onPreparation?.({totalMs:Math.round(performance.now()-prepareAt),stages:preparation});
      openingSurfacesReady=true;
      playing=false;version++;return true;
    },
    get openingNarrated(){return openingDemo?.phase==='waiting'&&openingDemo.narrated===true;},
    beginOpening(reduced=false){
      options.onOpening?.({stage:'arrival',report:activeReport.id,kind:activeReport.kind,demo:openingDemo?.phase,narrated:openingDemo?.narrated});
      if(openingDemo?.phase!=='waiting')return false;
      if(openingDemo.narrated){
        if(activeReport.kind==='classroom'){
          // Reuse the prepared clean board. Narration writes the cover once from
          // zero; never flash a finished preview that must be erased on playback.
          openingDemo=null;playing=false;clock.startWrite();
          options.onOpening?.({stage:'loading',report:activeReport.id,phase:clock.phase,progress:clock.slots[clock.active].progress});
          boards.forEach((_,i)=>draw(i,true));programScreen?.select(activeReport);setReportState();
          void assetPreload.start(pages,{courseText:pages.map(p=>chalkPageText(p,'zh')+'\n'+chalkPageText(p,'en')).join('\n')});if(pages.length>1)void load(1,undefined,{background:true}).catch(()=>{});
          void voice.select(voiceReport(activeReport),{autoplay:true}).then(()=>{
            options.onOpening?.({stage:'loaded',report:activeReport.id,phase:clock.phase,progress:clock.slots[clock.active].progress});
            void voice.prefetchAll();
          });
          return true;
        }
        return this.setReport(activeReport.id,{autoplay:true});
      }
      const demo=openingDemo;select(demo.page);openingDemo={...demo,phase:'writing',elapsed:0};
      if(reduced)staticPage();playing=true;return true;
    },
    finishOpening,
    toggleStorage(){voice.pause();openingDemo=null;if(storageRig){stored=!stored;if(!stored)screenHub?.report();if(stored)consoleButtons.forEach(b=>b.visible=false);playing=false;chalk.visible=false;eraser.visible=false;fallingDust.visible=false;updateStorageLabel();setReportState();}return stored;},
    setClarity(value){boardMipBias.value=value==='natural'?.15:0;},
    setPresence(value){present=Boolean(value);if(!present)void voice.setContextActive(false);},get present(){return present;},
    update,seek,revealCurrent,get navigationPage(){return requestedPage??(loadingError&&voice.manifest&&voice.state.started?narrationFrame(voice.manifest,voice.state.time).page:clock.page);},get reviewRemaining(){return boardReview.remaining(clock.page);},disabled,root:scene,get renderActive(){return renderActive&&!hydrating&&!stored&&storageMotion.ready&&storageProgress===0;},get hasSelection(){return hasSelection;},
    get progress(){return {page:clock.page-clock.startAt,total:clock.stopAt-clock.startAt+1};},
    screenAction:action=>{if(programScreen?.action(action)){screenHub?.report();return true;}voice.pause();openingDemo=null;return screenHub?.action(action)||seminarScreen?.action(action);},
    get programTab(){return programScreen?.tab||'reports';},
    screenWake:()=>screenHub?.wake(),get screenMode(){return screenHub?.state;},
    async setRenderActive(value){
      if(value===renderActive)return;renderActive=value;const epoch=++renderEpoch;
      if(!value){void voice.setContextActive(false);hydrating=false;chalk.visible=false;eraser.visible=false;fallingDust.visible=false;parkedErasers.forEach(e=>e.visible=true);return;}
      // Opening boards are paused and already painted/uploaded. Becoming visible
      // at the entrance must not reset and redraw six unchanged surfaces.
      if(openingDemo?.phase==='waiting'&&openingSurfacesReady&&boards.every(b=>b.canvas)&&clock.slots.every(slot=>slot.page<0||cache.has(slot.page))){hydrating=false;return;}
      // Returning to a prepared room reuses its ink and mechanism positions unchanged.
      if(boards.every(b=>b.canvas)&&(!hasSelection||cache.has(clock.page))&&clock.slots.every(slot=>slot.page<0||cache.has(slot.page))){hydrating=false;return;}
      hydrating=true;const resume={page:clock.page,phase:clock.phase,progress:clock.progress};
      try{
        const visible=[...new Set([...clock.slots.map(s=>s.page),hasSelection?clock.page:-1])].filter(i=>i>=0);
        for(const index of visible){await load(index);if(epoch!==renderEpoch)return;await new Promise(resolve=>typeof requestAnimationFrame==='function'?requestAnimationFrame(resolve):resolve());}
        if(epoch!==renderEpoch)return;
        if(clock.page===resume.page&&clock.phase===resume.phase)clock.elapsed=resume.progress*clock.duration;
        if(openingDemo?.phase!=='writing'){
          for(let pair=0;pair<3;pair++){const a=clock.slots[pair*2].page,b=clock.slots[pair*2+1].page;mix[pair]=targets[pair]=b>a?1:0;}
          if(hasSelection)targets[Math.floor(clock.active/2)]=mix[Math.floor(clock.active/2)]=clock.active%2;
        }
        boards.forEach(b=>{b.last='';b.wet=null;});eraserReturn=null;eraserPickup=null;eraser.userData.state='resting';
        previousTip=null;resetWipe();particles.forEach(p=>p.life=0);particlePositions.fill(-10000);
        hydrating=false;loadingError=null;update(0,openingDemo?.phase!=='writing');
      }catch(error){if(epoch===renderEpoch){loadingError=error;hydrating=false;}}
    },
    drawStudent(){if(!pages[clock.page]?.exerciseBoard)return false;if(!studentLottery.count)return studentLottery.chooseFile();return studentLottery.spin(activeReport.id+':'+clock.page);},importStudentRoster:()=>studentLottery.chooseFile(),setStudentRoster:text=>studentLottery.importRoster(text),get lotteryState(){return studentLottery.view(activeReport.id+':'+clock.page);},get inkStats(){return{...inkUploader.stats,rasterMs:lastRasterMs,width:boards[clock.active]?.canvas?.width||0,height:boards[clock.active]?.canvas?.height||0};},get preloadState(){return{boards:assetPreload.state,audio:voice.preloadState,prepared:cache.size,preparing:pending.size,nextPage:Math.min(clock.page+1,pages.length-1)+1,nextStage:pending.get(Math.min(clock.page+1,pages.length-1))?.stage||'',nextReady:cache.has(Math.min(clock.page+1,pages.length-1))};},get boardBackground(){return grain;},get boardCanvases(){return boards.map(b=>b.canvas);},get timeReadout(){return timePanels[0].text;},toggleTimeDisplay(){localClockDisplay=!localClockDisplay;return localClockDisplay;},get timeDisplayMode(){return localClockDisplay?'local':'progress';},get toolState(){return {chalk:chalk.position.toArray(),chalkColor:chalk.userData.inkColor,chalkMaterial:chalk.material.color.getHexString(),chalkEmissive:chalk.material.emissive.getHexString(),eraser:eraser.position.toArray(),eraserRotation:eraser.rotation.toArray(),pickup:eraserPickup?.elapsed??null,returning:eraserReturn?.elapsed??null,workElapsed:boardWork?.elapsed??null,eraserState:eraser.userData.state,eraseSeconds:eraseRun?.elapsed??null,eraseDuration:eraseRun?.duration??null,lifts:[...mix],transportPlaying:voice.transportPlaying};},get navigation(){return navigation;},get seeking(){return seeking;},reports,viewScale:options.viewScale||.72,get pages(){return pages;},get clock(){return clock;},get teachingClock(){return {period:lessonBudget.period,elapsed:lessonBudget.elapsed,thirdProof:lessonBudget.decision};},get report(){return activeReport;},consoleButtons,reportButtons,get hoverTargets(){return disabled?[]:[...timePanels.filter(p=>p.mesh.visible).map(p=>p.mesh),...countdownTargets.filter(t=>t.visible),...lotteryTargets,...touchButtons.filter(b=>!screenHub||!reportButtons.includes(b)||(screenHub.state.power&&screenHub.state.mode==='report')),...voicePanels.filter(panel=>panel.mesh.visible).map(panel=>panel.mesh),...(screenHub?.targets||[])];},setConsoleState,
    get highlightEnabled(){return highlightEnabled;},setHighlight(value){highlightEnabled=Boolean(value);if(!highlightEnabled){highlighter.hide();highlightState=null;}},get highlightTargets(){return measuredHighlights.get(clock.page)?.cues.map(c=>({id:c.id,row:c.row,side:c.side,begin:c.begin,duration:c.duration,rect:c.rect,visibleAt:c.visibleAt}))||[];},get highlightState(){return highlightState&&{page:highlightState.page,row:highlightState.row,side:highlightState.side,alpha:highlightState.alpha,age:highlightState.age};},
    setVoiceRate(value){return voice.setRate(value);},get voiceRate(){return voice.state.rate;},get voiceState(){return {...voice.state};},get voiceTone(){return voiceTone;},get voiceEnabled(){return voiceEnabled;},get voiceManifest(){return voice.manifest;},async voiceSeek(time){
      lessonBudget.configure(voice.manifest);lessonBudget.seek(time,voice.manifest?.boards.filter(b=>b.optionalProof)||[]);omittedProofPages.clear();boards.forEach(b=>b.last='');voice.pause();cancelBoardWork();highlighter.hide();highlightState=null;
      const target=voice.manifest?.boards.findLast(b=>b.start<=time);
      if(!target||!pages[target.page]?.orderedBoard)return voice.seek(time);
      const request=++seekRequest,epoch=generation;seeking=true;requestedPage=target.page;seekPinned=new Set([target.page]);
      try{
        const preparation=load(target.page),ok=await voice.seek(time,{ready:preparation});await preparation;
        if(request!==seekRequest||epoch!==generation)return false;
        const frame=narrationFrame(voice.manifest,voice.state.time,writingPlan(pageRows.get(target.page),guides.get(target.page)),erasePlans.get(target.page-6));
        syncNarrationClock(clock,frame,boardSlot);mix[Math.floor(clock.active/2)]=targets[Math.floor(clock.active/2)]=clock.active%2;
        boardHeights(mix[Math.floor(clock.active/2)]).forEach((h,s)=>boards[Math.floor(clock.active/2)*2+s].group.position.y=h);
        boards.forEach(b=>{b.last='';b.wet=null;});boards.forEach((_,i)=>draw(i,true));version++;return ok;
      }finally{if(request===seekRequest){seeking=false;requestedPage=null;seekPinned.clear();}}
    },skipClassroomActivity:()=>{const wait=classroomWaitAt(voice.manifest,voice.state.time,clock.page);if(wait){boards.forEach(b=>b.last='');version++;return voice.seek(wait.end+.001,{preservePlayback:true});}return stepExercise(1)?Promise.resolve(true):voice.skipActivity();},get exerciseFrame(){return exerciseFrames.get(clock.page)||null;},async toggleVoice(){if(loadingError){loadingError=null;assetRetry.clear();boardPreparation=null;}if(!activeReport.narration||!voiceEnabled){playing=hasSelection&&!playing;return true;}if(pages[clock.page]?.orderedBoard&&voice.state.phase==='paused'){const b=voice.manifest?.boards.find(b=>b.page===clock.page);if(b?.boardHoldSeconds>0&&voice.state.time>=b.end-b.boardHoldSeconds&&boardReview.remaining(clock.page)===0)await voice.seek(b.end-.03);}return voice.toggle();},
    async setVoiceTone(tone){
      const variants=activeReport.narration?.voices||[];if(tone!=='off'&&tone!=='original'&&!variants.some(v=>v.id===tone))throw Error('此报告尚无该音色');
      const bookmark=!voiceEnabled&&voiceBookmark?.report===activeReport.id?voiceBookmark:null,previous=bookmark?.manifest||voice.manifest,time=bookmark?.time??voice.state.time,started=bookmark?.started??voice.state.started,resume=!bookmark&&['playing','away','buffering','preparing'].includes(voice.state.phase);if(tone==='off')voiceBookmark={report:activeReport.id,manifest:previous,time,started,page:clock.page,progress:clock.progress};voiceTone=tone;voiceEnabled=tone!=='off';playing=false;
      if(!voiceEnabled){await voice.select(null);return true;}
      if(!await voice.select(voiceReport(activeReport)))return false;
      if(started&&time>0){let destination=mapNarrationPosition(previous,voice.manifest,time);if(bookmark&&(bookmark.page!==clock.page||Math.abs(bookmark.progress-clock.progress)>.001)){const b=voice.manifest.boards.find(b=>b.page===clock.page);if(b)destination=b.writeStart+(b.writeEnd-b.writeStart)*clock.progress;}await voice.seek(destination);}voiceBookmark=null;
      if(resume)await voice.toggle();return true;
    },
    get pendingReport(){return pendingReport;},
    preloadReports:()=>disabled?Promise.resolve([]):Promise.allSettled(reports.filter(r=>r.kind!=='classroom').map(prepareReport)),
    reportFocus:()=>scene.localToWorld(new THREE.Vector3(reportX+1.1,2.45,-11.34)),
    async setReport(id,{autoplay=false,loadVoice=true}={}){
      if(disabled)return false;
      openingDemo=null;voiceBookmark=null;assetPreload.cancel();
      const next=reports.find(r=>r.id===id);if(!next)throw new Error('未知报告');if(voiceTone!=='off'&&voiceTone!=='original'&&!next.narration?.voices?.some(v=>v.id===voiceTone))voiceTone='original';screenHub?.report();
      voice.setContextActive(false);
      if(storageRig){stored=false;storageRig.visible=true;updateStorageLabel();}
      seekRequest++;seeking=false;const request=++reportRequest;pendingReport=next;setReportState();const voicePreparation=voice.select(voiceEnabled&&loadVoice?voiceReport(next):null,{autoplay});
      try{
        const manifest=await prepareReport(next);if(request!==reportRequest)return false;
        // Keep the current talk intact until its replacement cover is available.
        generation++;lessonBudget.select(next.id);omittedProofPages.clear();navigation=manifest.navigation;pages=manifest.pages;activeReport=next;studentLottery.setCourse(next.courseId||next.id,next.id);programScreen?.select(next);clock=new LectureClock(pages.length);estimateDurations();hasSelection=true;if(navigation?.sections)clock.stopAt=navigation.sections[0].end;loadingError=null;
        clearPageCache();pending.clear();guides.clear();erasePlans.clear();pageRows.clear();resetWipe();
        boards.forEach(b=>{b.last='';b.wet=null;});targets.fill(0);eraserReturn=null;eraserPickup=null;eraser.visible=false;eraser.userData.state='parked';
        parkedErasers.forEach(e=>e.visible=true);chalk.visible=false;previousTip=null;lastWritePage=-1;wear=0;particles.forEach(p=>p.life=0);particlePositions.fill(-10000);dustGeometry.attributes.position.needsUpdate=true;
        playing=!next.narration||!voiceEnabled;version++;await load(0,manifest.cover);
        // Commit the prepared content independently of audio transfer readiness.
        if(request!==reportRequest)return false;
        // A new report starts on a clean board; there is no previous page to lift or erase.
        clock.startWrite();boards.forEach((_,i)=>draw(i));if(next.kind==='classroom'){void assetPreload.start(pages,{courseText:pages.map(p=>chalkPageText(p,'zh')+'\n'+chalkPageText(p,'en')).join('\n')});if(pages.length>1)void load(1,undefined,{background:true}).catch(()=>{});if(loadVoice&&voiceEnabled)void voicePreparation.then(()=>{if(request===reportRequest)return voice.prefetchAll();});}return true;
      }catch(error){if(request!==reportRequest)return false;void voice.select(null);throw error;}
      finally{if(request===reportRequest){pendingReport=null;setReportState();}}
    },
    setWoodTone(value){
      const old=trayHardware.tone,tone=trayHardware.setTone(value),stone=isCrystalScheme(tone);if(tone===old)return tone;
      tracks.forEach(track=>setTrackScheme(track,trayHardware.crystalMaterial,stone));
      hardware.back.color.set(stone?'#202124':'#243c32');
      boards.forEach(b=>{b.group.children[0].material.color.set(stone?'#ffffff':'#c9c5bb');for(const m of b.group.children){if(m.name==='Rail carriage bracket'||m.name==='Guide roller')m.visible=!stone;}});
      for(const root of [...pageControls.flatMap(p=>p.meshes),...cameraPanels.flatMap(p=>p.meshes),...consoleButtons,...voicePanels.map(p=>p.mesh),...timePanels.map(p=>p.mesh)]){root.userData.trayDarkInk=stone;root.traverse(m=>{if(m.material?.map&&m.material.color)m.material.color.set(stone?'#27313a':'#ffffff');});}
      if(stone!==isCrystalScheme(old)){paintBackground(blankCtx,128,64);blankTexture.needsUpdate=true;if(grain)grain.width=1;if(dust)dust.width=1;grain=dust=null;contentFadeQueue.length=0;boards.forEach(b=>{b.last='';b.fadeAge=1;b.inkBlend.value=1;});boards.forEach((_,i)=>draw(i,true));}
      if(stone)void trayHardware.prepareMinerals(renderer).then(ready=>{if(ready&&isCrystalScheme(trayHardware.tone)){paintBackground(blankCtx,128,64);blankTexture.needsUpdate=true;if(grain)grain.width=1;grain=null;boards.forEach(b=>b.last='');boards.forEach((_,i)=>draw(i,true));}}).catch(error=>{loadingError=error.message;});
      return tone;
    },get woodTone(){return trayHardware.tone;},
    setWritingSpeed(value){writingSpeed=Math.max(.25,Math.min(2,Number(value)||1));},
    get writingSpeed(){return writingSpeed;},
    get language(){return language;},copy:(index=clock.page)=>chalkCopy(pages[index],language),
    get writingStyle(){return writingStyle;},
    get mathStyle(){return mathStyle;},
    async setMathStyle(value){const next=value==='refined'?'refined':'mali-italic';if(next===mathStyle||disabled)return;const wasPlaying=playing,progress=clock.progress;playing=false;mathStyle=next;try{await this.setLanguage(language,true);clock.elapsed=progress*clock.duration;}finally{playing=wasPlaying;}},
    async setWritingStyle(value){const next=['refined','marck'].includes(value)?value:'mali-italic';if(next===writingStyle||disabled)return;const wasPlaying=playing,progress=clock.progress;playing=false;writingStyle=next;try{await this.setLanguage(language,true);clock.elapsed=progress*clock.duration;}finally{playing=wasPlaying;}},
    async setLanguage(value,force=false){
      if(disabled)return false;
      const next=value==='en'?'en':'zh';if(next===language&&!force)return;
      const request=++languageRequest,wasRevealed=[...revealedPages],time=voice.state.time,started=voice.state.started;translating=true;
      const visibleInk=['write','hold'].includes(clock.phase)&&clock.slots[clock.active]?.page===clock.page?{page:clock.page,progress:clock.slots[clock.active].progress}:null;
      seekRequest++;seeking=false;language=next;seminarScreen?.setLanguage(next);setConsoleState();setReportState();generation++;const epoch=generation,seekToken=seekRequest;loadingError=null;clearPageCache();pending.clear();guides.clear();erasePlans.clear();pageRows.clear();resetWipe();previousTip=null;
      boards.forEach(b=>{b.last='';b.wet=null;});version++;
      const ready=Promise.all([...new Set([clock.page,...clock.slots.map(s=>s.page)])].map(index=>load(index))).then(()=>{
        if(epoch!==generation||request!==languageRequest||seekToken!==seekRequest)return false;
        translatedInk=visibleInk;workManifest=voice.manifest;wasRevealed.forEach(p=>revealedPages.add(p));contentFadeQueue.length=0;
        // Translation is a presentation change, so paint it even while paused.
        boards.forEach((b,i)=>{b.last='';draw(i,true);});version++;return true;
      });
      try{if(voice.manifest&&started)await Promise.all([ready,voice.seek(time,{preservePlayback:true,ready})]);else await ready;return epoch===generation;}
      catch(error){loadingError=error;throw error;}finally{if(request===languageRequest)translating=false;}
    },
    setRange(start=0,end=pages.length-1){if(disabled)return Promise.resolve(false);hasSelection=true;seminarScreen?.select(navigation?.sections?.find(s=>s.start===start)?.id);clock.startAt=Math.max(0,Math.min(start,pages.length-1));clock.stopAt=Math.max(clock.startAt,Math.min(end,pages.length-1));return seek(start);},
    status:()=>disabled?'本层板书暂未开放':loadingError?loadingError.message:!hasSelection?'请在左侧智慧屏选择本次内容':`${clock.page-clock.startAt+1} / ${clock.stopAt-clock.startAt+1} · ${clock.ended?(navigation?.sections?'本节结束':'报告结束'):phaseNames[clock.phase]} · ${chalkCopy(pages[clock.page],language).title}`,
    get narrationCue(){
      const b=voice.manifest?.boards.find(b=>b.page===clock.page),t=voice.state.time;
      const c=b?.lineCues?.find(c=>t>=c.audioStart&&t<c.audioEnd);
      return c?{row:c.row,total:b.lineCues.length,text:c.text}:null;
    },
    get playing(){return present&&hasSelection&&(activeReport.narration&&voiceEnabled&&!openingDemo?voice.transportPlaying:playing)&&!clock.ended;},set playing(value){if(value&&loadingError){loadingError=null;assetRetry.clear();boardPreparation=null;}if(activeReport.narration&&voiceEnabled&&!openingDemo){if(!value)voice.pause();else if(voice.state.phase!=='playing')void voice.toggle();}else playing=hasSelection&&value;},
    skipOptionalProof:omitOptionalProof,
    async completePage(page=clock.page){if(!await seek(page))return false;const b=voice.manifest?.boards.find(b=>b.page===clock.page);if(b){const schedule=writingSchedule(b,writingPlan(pageRows.get(b.page),guides.get(b.page)));await voice.seek(schedule?Math.min(schedule.end,b.end-.25):b.writeEnd);workManifest=voice.manifest;completedWork.add('write:'+b.page+':end');}else staticPage();return true;},
    select,stepExercise,step(delta){if(stepExercise(delta))return Promise.resolve(true);return seek((requestedPage??clock.page)+delta,{preservePlayback:true});},rewrite(){select(clock.page);},staticPage,
    lift(pair,value){targets[pair]=THREE.MathUtils.clamp(Number(value),0,1);},
    heights:()=>[...targets],focus:(single=false)=>scene.localToWorld(new THREE.Vector3(boards[clock.active].group.position.x,single?boards[clock.active].group.position.y:(BOARD_LAYOUT.low+BOARD_LAYOUT.high)/2,-10.4+BOARD_MOUNT_OFFSET)),
    dispose(){inkUploader.dispose();assetPreload.cancel();unbindVoiceFocus();voice.dispose();cancelBoardWork();pageControls.forEach(panel=>panel.dispose());highlighter.dispose();voicePanels.forEach(panel=>panel.dispose());timePanels.forEach(panel=>panel.dispose());cameraPanels.forEach(panel=>panel.dispose());storageWell?.traverse(o=>{if(o.isMesh&&o.material!==options.floorMaterial)o.material.dispose();});renderEpoch++;screenHub?.dispose();programScreen?.dispose();seminarScreen?.dispose();trayHardware.dispose();hardware.dispose();reportTextures.forEach(t=>t.dispose());[reportHeader.mesh,...(programScreen?[]:reportButtons)].forEach(b=>b.traverse(o=>{o.geometry?.dispose();o.material?.dispose();}));trayChalkGeometry.dispose();trayChalkMaterials.forEach(m=>m.dispose());consoleTextures.forEach(t=>t.dispose());consoleButtons.forEach(b=>b.traverse(o=>{o.geometry?.dispose();o.material?.dispose();}));dustGeometry.dispose();dustMaterial.dispose();dotMap.dispose();chalk.geometry.dispose();chalk.material.dispose();eraser.geometry.dispose();felt.geometry.dispose();felt.material.dispose();boards.forEach(board=>{if(board.previousCanvas){board.previousInk.value.dispose();board.previousCanvas.width=1;board.previousCanvas.height=1;}if(board.texture!==blankTexture)board.texture.dispose();board.roughTexture?.dispose();if(board.canvas){board.canvas.width=1;board.canvas.height=1;}board.group.traverse(object=>{object.geometry?.dispose();object.material?.dispose();});});blankTexture.dispose();blankCanvas.width=1;for(const c of [grain,dust,wipeCanvas,erasedGrain,...cache.values()])if(c){c.width=1;c.height=1;}cache.clear();guides.clear();}
  };
}
import {drawPulley} from './pulley-icon.js?v=1';

