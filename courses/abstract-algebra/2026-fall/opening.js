(() => {
  'use strict';
  const dialog = document.getElementById('courseOpening');
  const root = document.getElementById('symmetry-particle-studies');
  const canvas = root.querySelector('.opening-grains');
  const caption = root.querySelector('.opening-caption');
  const quote = root.querySelector('.opening-quote');
  function showCaption(visible){caption.classList.toggle('is-visible',visible);quote.classList.toggle('is-visible',visible&&Boolean(quote.textContent));}
  const panel = document.getElementById('openingSettings');
  const toggle = document.getElementById('openingSettingsToggle');
  const boot = window.CourseOpeningBoot;
  const reduce = matchMedia('(prefers-reduced-motion: reduce)').matches;
  // Keep previous material preferences, but migrate old ten-second shots to
  // the new thirty-second complete switching interval once.
  const storageKey = 'courseOpeningAppearance.v3';
  const durationChoices = [30,45,60,90];
  const morphSpeedChoices=[.25,.5,.75,1,1.5];
  const defaults = Object.freeze({backgroundBrightness:160,gemPercent:1.5,titleScale:115,quoteScale:115,textFade:2.4,complexityEnabled:true,complexityAmount:.5,depthEnabled:true,wanderEnabled:true,wanderAmount:.22,cameraEnabled:true,backgroundEnabled:true,radiationEnabled:true,radiationAmount:.45,radiationFineOnly:true,grainTypes:Object.freeze([true,true,true,true,true,true]),morphSpeed:.5,spinEnabled:true,spinSpeed:.6,sceneDurations:Object.freeze([30,30,30,30,30,30,30,30,30,30]),sceneEnabled:Object.freeze([false,false,false,true,true,true,true,true,true,true])});
  const appearanceRanges={backgroundBrightness:[20,240],gemPercent:[0,5],titleScale:[80,160],quoteScale:[80,160],textFade:[.6,5]};
  const freshDefaults=()=>({...defaults,grainTypes:[...defaults.grainTypes],sceneEnabled:[...defaults.sceneEnabled],sceneDurations:[...defaults.sceneDurations]});
  let settings = freshDefaults();
  try {
    const current=localStorage.getItem(storageKey),saved=JSON.parse(current||localStorage.getItem('courseOpeningAppearance.v2')||'{}');
    for (const key of Object.keys(defaults)) {
      if (typeof defaults[key] === 'boolean' && typeof saved[key] === 'boolean') settings[key] = saved[key];
      else if (typeof defaults[key] === 'number' && Number.isFinite(saved[key])) settings[key] = Math.max(0,Math.min(1,saved[key]));
    }
    for(const [key,[min,max]] of Object.entries(appearanceRanges))settings[key]=Number.isFinite(saved[key])?Math.max(min,Math.min(max,saved[key])):defaults[key];
    if(Array.isArray(saved.grainTypes)&&saved.grainTypes.length===6&&saved.grainTypes.every(v=>typeof v==='boolean')&&saved.grainTypes.some(Boolean))settings.grainTypes=[...saved.grainTypes];
    if(Array.isArray(saved.sceneEnabled)){const selection=defaults.sceneEnabled.map((v,i)=>i<3?false:typeof saved.sceneEnabled[i]==='boolean'?saved.sceneEnabled[i]:v);if(selection.some(Boolean))settings.sceneEnabled=selection;}
    settings.morphSpeed=morphSpeedChoices.includes(saved.morphSpeed)?saved.morphSpeed:defaults.morphSpeed;
    settings.spinSpeed=Number.isFinite(saved.spinSpeed)?Math.max(0,Math.min(3,saved.spinSpeed)):defaults.spinSpeed;
    if(current&&Array.isArray(saved.sceneDurations))settings.sceneDurations=defaults.sceneDurations.map((value,i)=>durationChoices.includes(saved.sceneDurations[i])?saved.sceneDurations[i]:value);
  } catch (_) {}
  let film = null, initialization = null, visibilityTimer = 0, stage = 'loading', ownedFullscreen = false, entryVersion = 0;
  toggle.disabled=true;
  const startButton=root.querySelector('[data-start-animation]');
  function effective() {return {complexity:settings.complexityEnabled?settings.complexityAmount:0,depth:settings.depthEnabled?1:0,wander:settings.wanderEnabled?settings.wanderAmount:0,camera:!['outro','departing'].includes(stage)&&settings.cameraEnabled?1:0,background:settings.backgroundEnabled?1:0,radiation:!['outro','departing'].includes(stage)&&settings.radiationEnabled?settings.radiationAmount:0,spin:!['outro','departing'].includes(stage)&&settings.spinEnabled?settings.spinSpeed*Math.PI/180:0};}
  function syncSettings() {
    root.dataset.settings = JSON.stringify(settings);
    root.style.setProperty('--title-scale',settings.titleScale/100);root.style.setProperty('--quote-scale',settings.quoteScale/100);root.style.setProperty('--text-fade',settings.textFade+'s');
    panel.querySelectorAll('[data-appearance-range]').forEach(input=>{
      const key=input.dataset.appearanceRange,[min,max]=appearanceRanges[key];input.value=settings[key];input.disabled=key==='backgroundBrightness'&&!settings.backgroundEnabled;
      panel.querySelector('[data-appearance-output="'+key+'"]').textContent=key==='textFade'?settings[key].toFixed(1)+' 秒':settings[key]+'%';
      input.style.setProperty('--range-progress',(settings[key]-min)/(max-min)*100+'%');
    });
    root.classList.toggle('can-orbit',settings.depthEnabled&&!['outro','departing'].includes(stage));
    panel.querySelector('[data-morph-speed]').value=String(settings.morphSpeed);
    const spinInput=panel.querySelector('[data-spin-speed]');spinInput.value=String(settings.spinSpeed);spinInput.disabled=!settings.spinEnabled;
    spinInput.style.setProperty('--range-progress',(settings.spinSpeed/3*100)+'%');panel.querySelector('[data-spin-output]').textContent=settings.spinSpeed.toFixed(1)+'°/秒';
    panel.querySelectorAll('[data-scene-duration]').forEach(input=>input.value=String(settings.sceneDurations[Number(input.dataset.sceneDuration)]));
    panel.querySelectorAll('[data-scene-enabled]').forEach(input=>{const i=Number(input.dataset.sceneEnabled);input.checked=settings.sceneEnabled[i];input.disabled=input.checked&&settings.sceneEnabled.filter(Boolean).length===1;});
    panel.querySelectorAll('[data-grain-type]').forEach(input=>{const i=Number(input.dataset.grainType);input.checked=settings.grainTypes[i];input.disabled=input.checked&&settings.grainTypes.filter(Boolean).length===1;});
    panel.querySelector('[data-setting-toggle="radiationFineOnly"]').disabled=!settings.radiationEnabled;
    panel.querySelectorAll('[data-setting-toggle]').forEach(input=>input.checked=settings[input.dataset.settingToggle]);
    panel.querySelectorAll('[data-setting-range]').forEach(input=>{
      const key=input.dataset.settingRange, flag=key.replace('Amount','Enabled');
      input.value=Math.round(settings[key]*100); input.disabled=!settings[flag];
      panel.querySelector('[data-setting-output="'+key+'"]').textContent=input.value+'%';
      input.style.setProperty('--range-progress',input.value+'%');
    });
  }
  function updateSettings() {
    syncSettings();try {localStorage.setItem(storageKey,JSON.stringify(settings));} catch (_) {}
    if(film)film.refresh();
  }
  panel.addEventListener('input',event=>{
    const input=event.target;
    if(input.dataset.sceneEnabled!==undefined){const i=Number(input.dataset.sceneEnabled);if(!Number.isInteger(i)||i<3||i>=settings.sceneEnabled.length)return;const next=[...settings.sceneEnabled];next[i]=input.checked;if(!next.some(Boolean)){syncSettings();return;}settings.sceneEnabled=next;}
    else if(input.dataset.grainType!==undefined){const i=Number(input.dataset.grainType);if(!Number.isInteger(i)||i<0||i>5)return;const next=[...settings.grainTypes];next[i]=input.checked;if(!next.some(Boolean)){syncSettings();return;}settings.grainTypes=next;}
    else if(input.dataset.appearanceRange&&appearanceRanges[input.dataset.appearanceRange]&&Number.isFinite(Number(input.value))){const key=input.dataset.appearanceRange,[min,max]=appearanceRanges[key];settings[key]=Math.max(min,Math.min(max,Number(input.value)));}
    else if(input.dataset.settingToggle)settings[input.dataset.settingToggle]=input.checked;
    else if(input.dataset.settingRange)settings[input.dataset.settingRange]=Number(input.value)/100;
    else if(input.hasAttribute('data-spin-speed')&&Number.isFinite(Number(input.value)))settings.spinSpeed=Math.max(0,Math.min(3,Number(input.value)));
    else if(input.hasAttribute('data-morph-speed')&&morphSpeedChoices.includes(Number(input.value)))settings.morphSpeed=Number(input.value);
    else if(input.dataset.sceneDuration!==undefined&&durationChoices.includes(Number(input.value)))settings.sceneDurations[Number(input.dataset.sceneDuration)]=Number(input.value);
    else return;
    updateSettings();
  });
  panel.querySelector('[data-settings-reset]').addEventListener('click',()=>{settings=freshDefaults();film?.resetPolyhedra();updateSettings();});
  function showControls() {
    dialog.classList.add('has-pointer-controls');clearTimeout(visibilityTimer);
    visibilityTimer=setTimeout(()=>{if(panel.hidden)dialog.classList.remove('has-pointer-controls');},2400);
  }
  function closeSettings(restoreFocus=false) {
    panel.hidden=true;dialog.classList.remove('settings-open');toggle.setAttribute('aria-expanded','false');
    if(restoreFocus)toggle.focus({preventScroll:true});showControls();
  }
  toggle.addEventListener('click',()=>{
    if(!panel.hidden){closeSettings(true);return;}
    panel.hidden=false;dialog.classList.add('settings-open');toggle.setAttribute('aria-expanded','true');
    panel.querySelector('[data-setting-toggle]').focus({preventScroll:true});
  });
  panel.querySelector('[data-settings-close]').addEventListener('click',()=>closeSettings(true));
  dialog.addEventListener('pointermove',showControls);
  dialog.addEventListener('pointerdown',event=>{if(!panel.hidden&&!panel.contains(event.target)&&!toggle.contains(event.target))closeSettings();});
  dialog.addEventListener('focusin',event=>{if(event.target===toggle||panel.contains(event.target))showControls();});
  function requestCourseEntry(){
    if(stage==='playing'){
      stage='outro';root.dataset.stage=stage;dialog.classList.add('opening-outro');closeSettings();dialog.focus({preventScroll:true});
      window.CourseOpeningVoice?.stop();film.outro();syncSettings();showControls();
    }else if(stage==='outro'&&film.outroReady()){stage='departing';root.dataset.stage=stage;closeSettings();dialog.focus({preventScroll:true});film.depart();}
  }
  function leaveOpening() {
    entryVersion++;stage='closed';root.dataset.stage=stage;toggle.disabled=true;
    if(ownedFullscreen&&document.fullscreenElement){ownedFullscreen=false;document.exitFullscreen().catch(()=>{});}
    window.CourseOpeningAudio?.stop();window.CourseOpeningVoice?.stop();
    if(film)film.stop();boot.stop();panel.hidden=true;dialog.classList.remove('settings-open','has-pointer-controls');toggle.setAttribute('aria-expanded','false');clearTimeout(visibilityTimer);
    if(dialog.open)dialog.close();document.body.classList.remove('opening-active');document.documentElement.classList.remove('course-opening-pending');
    const main=document.getElementById('main');if(main){main.setAttribute('tabindex','-1');main.focus({preventScroll:true});}
  }
  async function openOpening() {
    if(root.dataset.contextLost==='true')return;
    const alreadyLoading=dialog.open&&dialog.classList.contains('opening-loading');
    if(dialog.open&&!alreadyLoading)return;
    if(!dialog.open){dialog.classList.remove('opening-outro');boot.start();}
    const entry=++entryVersion;stage='loading';root.dataset.stage=stage;toggle.disabled=true;
    try {
      if(!initialization)initialization=initialize();await initialization;
      if(entry===entryVersion&&dialog.open){stage='ready';root.dataset.stage=stage;boot.ready();dialog.classList.remove('opening-loading');dialog.classList.add('opening-awaiting-start');}
    }catch(error){if(entry===entryVersion){root.dataset.unavailable='true';leaveOpening();initialization=null;}}
  }
  function startAnimation() {
    if(stage!=='ready'||!film)return;
    const entry=++entryVersion;
    stage='starting';root.dataset.stage=stage;startButton.disabled=true;boot.finish();
    window.CourseOpeningAudio?.start();window.CourseOpeningVoice?.unlock();
    // Fullscreen is an enhancement: playback must not wait for permission or a
    // browser promise that may never settle (notably in mobile web views).
    if(!document.fullscreenElement&&document.fullscreenEnabled!==false&&typeof root.requestFullscreen==='function'){
      try {
        Promise.resolve(root.requestFullscreen({navigationUI:'hide'})).then(()=>{
          if(document.fullscreenElement!==root)return;
          if(entry!==entryVersion||stage!=='playing'||!dialog.open){
            if(stage!=='playing')document.exitFullscreen().catch(()=>{});
            return;
          }
          ownedFullscreen=true;
        }).catch(()=>{}); // Keep playing in the page if fullscreen is rejected.
      }catch(_){ /* Older implementations can throw synchronously; keep playing. */ }
    }
    ownedFullscreen=document.fullscreenElement===root||ownedFullscreen;
    stage='playing';root.dataset.stage=stage;
    dialog.classList.remove('opening-loading','opening-awaiting-start');dialog.classList.add('opening-ready');
    toggle.disabled=false;dialog.focus({preventScroll:true});film.play();
  }
  dialog.addEventListener('click',()=>{if(stage==='ready')startAnimation();});
  dialog.addEventListener('keydown',event=>{
    if((event.key===' '||event.key==='Enter'&&stage==='outro')&&!event.repeat&&!panel.contains(event.target)){
      event.preventDefault();if(stage==='ready')startAnimation();else requestCourseEntry();
    }
  });
  dialog.addEventListener('wheel',event=>{
    if(stage!=='playing'||panel.contains(event.target)||event.ctrlKey||Math.abs(event.deltaY)<.5)return;
    event.preventDefault();film.direction(event.deltaY>0?1:-1);showControls();
  },{passive:false});
  document.addEventListener('fullscreenchange',()=>{
    if(stage!=='playing')return;
    if(document.fullscreenElement===root)ownedFullscreen=true;
    else if(!document.fullscreenElement){ownedFullscreen=false;dialog.focus({preventScroll:true});film?.refresh();showControls();}
  });
  dialog.addEventListener('cancel',event=>{event.preventDefault();if(!panel.hidden)closeSettings(true);});
  panel.querySelector('[data-enter-course]').addEventListener('click',requestCourseEntry);
  document.querySelector('[data-replay-opening]').addEventListener('click',openOpening);
  canvas.addEventListener('webglcontextlost',event=>{
    event.preventDefault();leaveOpening();if(film)film.dispose();film=null;initialization=null;
    root.dataset.contextLost='true';delete root.dataset.ready;delete root._openingPreview;
  });
  canvas.addEventListener('webglcontextrestored',()=>{delete root.dataset.contextLost;});
  window.courseOpeningControllerReady=true;syncSettings();
  const paint=()=>new Promise(resolve=>requestAnimationFrame(resolve));
  async function initialize() {
    const geometry=window.CourseOpeningGeometry, materials=window.CourseOpeningMaterials, cameraRig=window.CourseOpeningCamera;
    const gl=canvas.getContext('webgl',{alpha:false,antialias:false,preserveDrawingBuffer:true});
    if(!gl||!geometry||!materials||!cameraRig)throw new Error('Opening unavailable');
    // IDs 0–2 are retired; keep saved IDs stable without preparing removed figures.
    const N=geometry.count,targets=new Array(geometry.captions.length),normals=new Array(geometry.captions.length);
    boot.advance(22,'生成对称图形');await paint();
    for(let i=3;i<geometry.captions.length;i++){
      targets[i]=geometry.create3D(i);normals[i]=geometry.createNormals(i);root.dataset.prepared=String(i-2);boot.advance(22+(i-2)/(geometry.captions.length-3)*55,i===9?'绘制伽罗瓦沙像':i===8?'绘制高斯正十七边形':i===7?'构造圆与 Möbius 带':i===6?'构造五种正多面体':i===5?'铸造万环之环':i===4?'生成 Julia 分形':'生成对称图形');await paint();
    }
    const closingGeometry=window.CourseOpeningOutro.create(N);
    cameraRig.setFocuses(Array.from({length:geometry.captions.length},(_,index)=>index<3?[0,0,0]:geometry.closeupFocus(index)));
    boot.advance(82,'雕琢沙粒质感');await paint();
    function compile(type, source) {
      const shader = gl.createShader(type);
      gl.shaderSource(shader, source); gl.compileShader(shader);
      if (!gl.getShaderParameter(shader, gl.COMPILE_STATUS)) throw new Error(gl.getShaderInfoLog(shader));
      return shader;
    }
    function link(v, f) {
      const program = gl.createProgram();
      gl.attachShader(program, compile(gl.VERTEX_SHADER, v));
      gl.attachShader(program, compile(gl.FRAGMENT_SHADER, f));
      gl.linkProgram(program);
      if (!gl.getProgramParameter(program, gl.LINK_STATUS)) throw new Error(gl.getProgramInfoLog(program));
      return program;
    }
    function buffer(data, usage) {
      const result = gl.createBuffer(); gl.bindBuffer(gl.ARRAY_BUFFER, result);
      gl.bufferData(gl.ARRAY_BUFFER, data, usage); return result;
    }
    const program = link(materials.vertex, materials.fragment), background = link(materials.backgroundVertex, materials.backgroundFragment);
    const backdrop=window.CourseOpeningBackdrop,lettering=backdrop.create(gl),letterProgram=link(backdrop.vertex,backdrop.fragment);
    const narration=window.CourseOpeningNarration.create(quote,backdrop.scenes);
    const letterLoc={pos:gl.getAttribLocation(letterProgram,'pos'),visibility:gl.getUniformLocation(letterProgram,'visibility'),texture:gl.getUniformLocation(letterProgram,'lettering'),sweepTime:gl.getUniformLocation(letterProgram,'sweepTime'),sweepEnabled:gl.getUniformLocation(letterProgram,'sweepEnabled')};
    let captionOpacity=0;
    const quad = buffer(new Float32Array([-1,-1,1,-1,-1,1,-1,1,1,-1,1,1]), gl.STATIC_DRAW);
    const initialScene=settings.sceneEnabled.findIndex((on,i)=>i>=3&&on);
    let source=targets[initialScene],destination=targets[initialScene],normalSource=normals[initialScene],normalDestination=normals[initialScene],extrusionFrom=initialScene<5?1:0,extrusionTo=extrusionFrom;
    const sourceBuffer=buffer(source,gl.DYNAMIC_DRAW),destinationBuffer=buffer(destination,gl.DYNAMIC_DRAW);
    const normalSourceBuffer=buffer(normalSource,gl.DYNAMIC_DRAW),normalDestinationBuffer=buffer(normalDestination,gl.DYNAMIC_DRAW);
    let seed=317129;const grains=new Float32Array(N*4);
    for(let i=0;i<grains.length;i++){seed=(Math.imul(seed,1664525)+1013904223)>>>0;grains[i]=seed/4294967296;}
    const grainBuffer=buffer(grains,gl.STATIC_DRAW);
    const loc={source:gl.getAttribLocation(program,'start'),destination:gl.getAttribLocation(program,'finish'),normalSource:gl.getAttribLocation(program,'normalStart'),normalDestination:gl.getAttribLocation(program,'normalFinish'),grain:gl.getAttribLocation(program,'grain'),quad:gl.getAttribLocation(background,'pos')};
    for(const name of ['progress','aspect','dpr','time','gemShare','outroFall','outroExit','complexity','depth','wander','camera','radiation','viewAngles','viewTarget','viewZoom','objectSpin','extrusionFrom','extrusionTo','twoSided','radiationFineOnly','grainTypes[0]'])loc[name]=gl.getUniformLocation(program,name);
    const bgLoc={};for(const name of ['time','aspect','camera','background','stageLight','viewAngles','viewTarget','viewZoom'])bgLoc[name]=gl.getUniformLocation(background,name);
    function attribute(data,location,size){gl.bindBuffer(gl.ARRAY_BUFFER,data);gl.enableVertexAttribArray(location);gl.vertexAttribPointer(location,size,gl.FLOAT,false,0,0);}
    const baseTransitions=[4200,4200,4200,5200,5400,5000,5000,5000,5000,5000],entranceHold=1500;
    const selectedScenes=()=>settings.sceneEnabled.flatMap((on,i)=>i>=3&&on?[i]:[]);
    let order=selectedScenes();
    let transitions=order.map(id=>baseTransitions[id]/settings.morphSpeed);
    let holds=order.map((id,index)=>settings.sceneDurations[id]*1000-transitions[index]);
    let timeline=window.CourseOpeningTimeline.create({holds,transitions});
    const makeStarts=()=>holds.map((_,i)=>holds.slice(0,i).reduce((sum,x,j)=>sum+x+transitions[j],0));
    let starts=makeStarts();
    let scene=initialScene,progress=1,moving=false,active=false,sequence=false,entrance=false,elapsed=0,time=0,previous=0,raf=0,pair=initialScene+':'+initialScene;
    const visual={camera:0,background:0,radiation:0,spin:0};
    let outro=null;
    let spinAngle=0,routeOffset=0,cameraBridge=null,entrancePose=null,entranceDuration=transitions[0];
    const orbit={pitch:0,yaw:0,targetPitch:0,targetYaw:0,pointer:null,solid:-1,x:0,y:0};
    const ease=t=>t*t*t*(t*(t*6-15)+10);
    function snapshot(withEffects=false,atTime=time,world=true){
      const e=ease(progress),arch=Math.sin(Math.PI*e),result=new Float32Array(N*3),appearance=effective(),cosine=Math.cos(spinAngle),sine=Math.sin(spinAngle);
      for(let i=0;i<N;i++){
        const k=i*3,g=i*4,dx=destination[k]-source[k],dy=destination[k+1]-source[k+1],drift=arch*Math.min(.022,Math.hypot(dx,dy)*.16);
        let x=source[k]+dx*e-dy*arch*.28+Math.sin(grains[g]*19+e*6.283)*drift;
        let y=source[k+1]+dy*e+dx*arch*.28+Math.cos(grains[g+1]*23-e*6.283)*drift;
        const fromZ=source[k+2]*(1-extrusionFrom+extrusionFrom*appearance.depth),toZ=destination[k+2]*(1-extrusionTo+extrusionTo*appearance.depth);
        let z=fromZ+(toZ-fromZ)*e;
        if(withEffects){
          const normal=[0,0,0];
          for(let axis=0;axis<3;axis++){const face=axis===2?1:0,a=normalSource[k+axis]+(face-normalSource[k+axis])*extrusionFrom*(1-appearance.depth),b=normalDestination[k+axis]+(face-normalDestination[k+axis])*extrusionTo*(1-appearance.depth);normal[axis]=a+(b-a)*e;}
          const escaped=materials.radiationOffset(x,y,z,grains[g],grains[g+1],grains[g+2],grains[g+3],atTime,visual.radiation,normal,settings.radiationFineOnly);
          const d=materials.localOffset(x,y,grains[g],grains[g+1],grains[g+2],grains[g+3],atTime,appearance.wander);
          x+=d[0]*(1-escaped.chosen)+escaped.offset[0];y+=d[1]*(1-escaped.chosen)+escaped.offset[1];z+=escaped.offset[2];
        }
        result[k]=world?x*cosine-y*sine:x;result[k+1]=world?x*sine+y*cosine:y;result[k+2]=z;
      }return result;
    }
    function snapshotNormals(){const e=ease(progress),out=new Float32Array(N*3),flat=1-effective().depth;for(let i=0;i<out.length;i++){const face=i%3===2?1:0,a=normalSource[i]+(face-normalSource[i])*extrusionFrom*flat,b=normalDestination[i]+(face-normalDestination[i])*extrusionTo*flat;out[i]=a+(b-a)*e;}return out;}
    function upload(){for(const [buf,data] of [[sourceBuffer,source],[destinationBuffer,destination],[normalSourceBuffer,normalSource],[normalDestinationBuffer,normalDestination]]){gl.bindBuffer(gl.ARRAY_BUFFER,buf);gl.bufferSubData(gl.ARRAY_BUFFER,0,data);}}
    function updateCaption(){const text=geometry.captions[scene];for(const field of ['title','zh'])root.querySelector('[data-caption-'+field+']').textContent=text[field];narration.setScene(scene,timeline.state().cycles);quote.classList.remove('is-visible');canvas.setAttribute('aria-label',text.title+'。'+text.zh+'。'+text.en);root.querySelectorAll('[data-drag-hint]').forEach(el=>el.textContent=scene===7?'分别拖动圆与 Möbius 带':scene===6?'分别拖动五个多面体':'拖动旋转');}

    function syncTimeline(state){
      const from=order[state.from],to=order[state.to],key=from+':'+to;
      if(key!==pair){pair=key;source=targets[from];destination=targets[to];normalSource=normals[from];normalDestination=normals[to];extrusionFrom=from<5?1:0;extrusionTo=to<5?1:0;upload();}
      progress=state.progress;moving=state.moving;
      const label=order[state.moving?(state.direction>0?state.to:state.from):state.scene];
      if(scene!==label&&!state.moving){scene=label;updateCaption();}
      const spent=state.direction>0?state.holdElapsed:state.holdDuration-state.holdElapsed;
      const remaining=state.direction>0?state.holdDuration-state.holdElapsed:state.holdElapsed;
      showCaption(!state.moving&&(order.length===1||spent>420&&remaining>settings.textFade*1000+100));
    }
    function baseCameraPose(){
      const state=timeline.state(),mapped={...state,from:order[state.from],to:order[state.to],scene:order[state.scene]};
      const pose=cameraRig.sampleTimeline(mapped,{holds,transitions,starts,duration:timeline.duration,phaseOffset:routeOffset,sceneIds:order});
      if(entrance)return cameraRig.blend(entrancePose||{angles:[0,0,0],zoom:1,target:[0,0,0]},pose,ease(progress));
      return cameraBridge?cameraRig.blend(cameraBridge.from,pose,ease(cameraBridge.elapsed/cameraBridge.duration)):pose;
    }
    function cameraPose(){
      if(outro)return outro.view;
      const state=timeline.state(),pose=baseCameraPose();
      let target=pose.target.map(value=>value*visual.camera);
      if(!settings.depthEnabled&&!state.moving&&order[state.scene]<5)target[2]=0;
      target=materials.rotateObject(target,spinAngle);
      return {angles:[pose.angles[0]*visual.camera+orbit.pitch,pose.angles[1]*visual.camera+orbit.yaw,pose.angles[2]*visual.camera],target,zoom:Math.max(1,1+(pose.zoom-1)*visual.camera),perspective:Math.max(visual.camera,settings.depthEnabled?1:0)};
    }
    function rebuildDurations(){
      const nextOrder=selectedScenes(),nextTransitions=nextOrder.map(id=>baseTransitions[id]/settings.morphSpeed);
      const next=nextOrder.map((id,i)=>settings.sceneDurations[id]*1000-nextTransitions[i]);
      if(nextOrder.join(':')===order.join(':')&&next.every((v,i)=>v===holds[i])&&nextTransitions.every((v,i)=>v===transitions[i]))return;
      const previousPose=baseCameraPose(),old=timeline.state(),oldPhase=old.position/timeline.duration+routeOffset;
      const oldFrom=order[old.from],oldTo=order[old.to],oldScene=order[old.scene];
      const captured=snapshot(false,time,false),capturedNormals=snapshotNormals();
      const retainedEntrance=entrance&&nextOrder.includes(scene);
      order=nextOrder;holds=next;transitions=nextTransitions;starts=makeStarts();
      timeline=window.CourseOpeningTimeline.create({holds,transitions});timeline.setDirection(old.direction);
      const fromSlot=order.indexOf(oldFrom),toSlot=order.indexOf(oldTo),sceneSlot=order.indexOf(oldScene);
      const retainedMorph=!entrance&&old.moving&&order.length>1&&fromSlot>=0&&toSlot===(fromSlot+1)%order.length;
      let needsFormation=false,position=0;
      if(retainedEntrance)position=starts[order.indexOf(scene)];
      else if(retainedMorph)position=starts[fromSlot]+holds[fromSlot]+old.progress*transitions[fromSlot];
      else if(!entrance&&!old.moving&&sceneSlot>=0)position=starts[sceneSlot]+old.holdElapsed/old.holdDuration*(order.length===1?timeline.duration:holds[sceneSlot]);
      else{const targetSlot=order.includes(scene)?order.indexOf(scene):0;position=starts[targetSlot];needsFormation=true;}
      timeline.seek(position+old.cycles*timeline.duration);
      routeOffset=oldPhase-timeline.state().position/timeline.duration;routeOffset-=Math.floor(routeOffset);cameraBridge=null;
      if(retainedEntrance){entranceDuration=transitions[order.indexOf(scene)];if(elapsed>entranceHold)elapsed=entranceHold+progress*entranceDuration;}
      else if(needsFormation&&!reduce){
        scene=order[timeline.state().scene];source=captured;normalSource=capturedNormals;destination=targets[scene];normalDestination=normals[scene];
        extrusionFrom=0;extrusionTo=scene<5?1:0;pair='selection';progress=0;moving=true;entrance=true;entrancePose=previousPose;
        entranceDuration=transitions[timeline.state().scene];elapsed=entranceHold;sequence=true;upload();updateCaption();showCaption(false);
      }else{entrance=false;entrancePose=null;syncTimeline(timeline.state());}
      if(!entrance){
        const nextPose=baseCameraPose();
        const difference=Math.max(Math.abs(previousPose.zoom-nextPose.zoom),...previousPose.angles.map((x,i)=>Math.abs(x-nextPose.angles[i])),...previousPose.target.map((x,i)=>Math.abs(x-nextPose.target[i])));
        if(difference>1e-8)cameraBridge={from:previousPose,elapsed:0,duration:Math.max(3000,Math.abs(Math.log(previousPose.zoom/nextPose.zoom))/.12*1000)};
      }
    }
    function endOrbit(event){
      if(orbit.pointer===null||event&&event.pointerId!==orbit.pointer)return;
      if(root.hasPointerCapture(orbit.pointer))root.releasePointerCapture(orbit.pointer);
      orbit.pointer=null;orbit.solid=-1;delete root.dataset.draggingSolid;root.classList.remove('is-orbiting');previous=0;queue();
    }
    function beginOrbit(event){
      if(stage!=='playing'||!settings.depthEnabled||event.button!==0||!event.isPrimary||panel.contains(event.target)||event.target.closest('button,a,input,select,summary'))return;
      orbit.solid=-1;
      if(scene===6||scene===7){
        if(entrance||moving)return;
        const rect=canvas.getBoundingClientRect(),ray=window.CourseOpeningPolyhedra.screenRay(event.clientX-rect.left,event.clientY-rect.top,rect.width,rect.height,cameraPose(),spinAngle);
        orbit.solid=scene===7?geometry.pickTopology(ray):geometry.pickPolyhedron(ray);if(orbit.solid<0)return;root.dataset.draggingSolid=String(orbit.solid);
      }
      orbit.pointer=event.pointerId;orbit.x=event.clientX;orbit.y=event.clientY;
      root.setPointerCapture(event.pointerId);root.classList.add('is-orbiting');event.preventDefault();queue();
    }
    function moveOrbit(event){
      if(event.pointerId!==orbit.pointer)return;
      if(orbit.solid>=0){
        const rotation=window.CourseOpeningPolyhedra.dragRotation(event.clientX-orbit.x,event.clientY-orbit.y,cameraPose(),spinAngle);
        if(scene===7)geometry.rotateTopology(orbit.solid,rotation.axis,rotation.angle);else geometry.rotatePolyhedron(orbit.solid,rotation.axis,rotation.angle);upload();
        orbit.x=event.clientX;orbit.y=event.clientY;event.preventDefault();draw();queue();return;
      }
      const control=cameraRig.manual;
      orbit.targetYaw+=(event.clientX-orbit.x)*control.yawPerPixel;
      orbit.targetPitch=Math.max(-control.pitchLimit,Math.min(control.pitchLimit,orbit.targetPitch+(event.clientY-orbit.y)*control.pitchPerPixel));
      orbit.x=event.clientX;orbit.y=event.clientY;event.preventDefault();queue();
    }
    root.addEventListener('pointerdown',beginOrbit);root.addEventListener('pointermove',moveOrbit);
    root.addEventListener('pointerup',endOrbit);root.addEventListener('pointercancel',endOrbit);root.addEventListener('lostpointercapture',endOrbit);
    function draw(){
      if(!dialog.open)return;
      const rect=canvas.getBoundingClientRect(),ratio=Math.min(2,window.devicePixelRatio||1),width=Math.max(1,Math.round(rect.width*ratio)),height=Math.max(1,Math.round(rect.height*ratio));
      if(geometry.fitGalois(rect.width<700&&rect.height<700))upload();
      if(canvas.width!==width||canvas.height!==height){canvas.width=width;canvas.height=height;}
      const view=cameraPose();
      lettering.update(scene,rect.width,rect.height,ratio);
      gl.viewport(0,0,width,height);gl.disable(gl.DEPTH_TEST);gl.depthMask(false);gl.disable(gl.BLEND);gl.useProgram(background);
      gl.uniform1f(bgLoc.time,time);gl.uniform1f(bgLoc.aspect,width/height);gl.uniform1f(bgLoc.camera,view.perspective);gl.uniform3fv(bgLoc.viewAngles,view.angles);gl.uniform3fv(bgLoc.viewTarget,view.target);gl.uniform1f(bgLoc.viewZoom,view.zoom);gl.uniform1f(bgLoc.background,visual.background);gl.uniform1f(bgLoc.stageLight,settings.backgroundBrightness/100);
      attribute(quad,loc.quad,2);gl.drawArrays(gl.TRIANGLES,0,6);
      gl.useProgram(letterProgram);attribute(quad,letterLoc.pos,2);lettering.bind();gl.uniform1i(letterLoc.texture,0);gl.uniform1f(letterLoc.visibility,captionOpacity);gl.uniform1f(letterLoc.sweepTime,time%24);gl.uniform1f(letterLoc.sweepEnabled,!reduce&&settings.backgroundEnabled?1:0);gl.enable(gl.BLEND);gl.blendFunc(gl.SRC_ALPHA,gl.ONE_MINUS_SRC_ALPHA);gl.drawArrays(gl.TRIANGLES,0,6);
      gl.depthMask(true);gl.clearDepth(1);gl.clear(gl.DEPTH_BUFFER_BIT);gl.enable(gl.DEPTH_TEST);gl.depthFunc(gl.LEQUAL);
      gl.useProgram(program);attribute(sourceBuffer,loc.source,3);attribute(destinationBuffer,loc.destination,3);attribute(normalSourceBuffer,loc.normalSource,3);attribute(normalDestinationBuffer,loc.normalDestination,3);attribute(grainBuffer,loc.grain,4);
      gl.enable(gl.BLEND);gl.blendFunc(gl.SRC_ALPHA,gl.ONE_MINUS_SRC_ALPHA);
      gl.uniform1f(loc.progress,progress);gl.uniform1f(loc.aspect,width/height);gl.uniform1f(loc.dpr,ratio*Math.max(1,Math.min(1.4,rect.height/800)));gl.uniform1f(loc.time,time);
      const appearance=effective();for(const name of ['complexity','depth','wander'])gl.uniform1f(loc[name],appearance[name]);gl.uniform1f(loc.camera,view.perspective);gl.uniform3fv(loc.viewAngles,view.angles);gl.uniform3fv(loc.viewTarget,view.target);gl.uniform1f(loc.viewZoom,view.zoom);gl.uniform1f(loc.objectSpin,spinAngle);gl.uniform1f(loc.twoSided,scene===7&&!outro?1:0);gl.uniform1f(loc.extrusionFrom,extrusionFrom);gl.uniform1f(loc.extrusionTo,extrusionTo);gl.uniform1f(loc.radiation,visual.radiation);gl.uniform1f(loc.radiationFineOnly,settings.radiationFineOnly?1:0);gl.uniform1fv(loc['grainTypes[0]'],settings.grainTypes.map(Number));gl.uniform1f(loc.gemShare,settings.gemPercent/100);gl.uniform1f(loc.outroFall,outro&&!reduce?(['hold','depart'].includes(outro.phase)?1:outro.phase==='form'?Math.max(0,(progress-.75)/.25):0):0);gl.uniform1f(loc.outroExit,outro?.phase==='depart'?outro.elapsed/(reduce?170:1000):-1);
      gl.drawArrays(gl.POINTS,0,N);root.dataset.scene=String(scene);root.dataset.progress=progress.toFixed(4);root.dataset.time=time.toFixed(3);root.dataset.direction=String(timeline.state().direction);root.dataset.cycles=String(timeline.state().cycles);root.dataset.spin=spinAngle.toFixed(6);
    }
    function beginOutro(){
      const view=cameraPose(),captured=snapshot(false,time,true),capturedNormals=snapshotNormals();
      const cosine=Math.cos(spinAngle),sine=Math.sin(spinAngle);
      for(let i=0;i<capturedNormals.length;i+=3){const x=capturedNormals[i],y=capturedNormals[i+1];capturedNormals[i]=cosine*x-sine*y;capturedNormals[i+1]=sine*x+cosine*y;}
      endOrbit();sequence=false;entrance=false;moving=false;cameraBridge=null;spinAngle=0;
      orbit.pitch=orbit.yaw=orbit.targetPitch=orbit.targetYaw=0;
      source=destination=captured;normalSource=normalDestination=capturedNormals;extrusionFrom=extrusionTo=0;progress=1;
      outro={phase:'return',elapsed:0,from:view,view};root.dataset.outro='return';
      root.querySelector('[data-outro-hint]').textContent='镜头归位 · 沙粒落字';
      panel.querySelector('[data-enter-course]').disabled=true;showCaption(false);upload();active=true;previous=0;queue();
    }
    function advanceOutro(dt){
      outro.elapsed+=dt;
      if(outro.phase==='depart'){if(outro.elapsed>=(reduce?800:4200))leaveOpening();return;}
      const neutral={angles:[0,0,0],target:[0,0,0],zoom:1,perspective:0};
      if(outro.phase==='return'){
        const amount=reduce?1:ease(Math.min(1,outro.elapsed/900));
        outro.view={...cameraRig.blend(outro.from,neutral,amount),perspective:outro.from.perspective*(1-amount)};
        if(amount===1){
          outro.phase='form';outro.elapsed=0;outro.view=neutral;root.dataset.outro='form';
          destination=closingGeometry.positions;normalDestination=closingGeometry.normals;progress=0;upload();
          canvas.setAttribute('aria-label','Algebra Ⅰ. Sheng Meng.');
        }
      }else if(outro.phase==='form'){
        progress=reduce?1:Math.min(1,outro.elapsed/3600);
        if(progress===1){outro.phase='hold';root.dataset.outro='hold';panel.querySelector('[data-enter-course]').disabled=false;root.querySelector('[data-outro-hint]').textContent='按回车，落沙后进入课程';}
      }
    }
    function depart(){outro.phase='depart';outro.elapsed=0;root.dataset.outro='depart';panel.querySelector('[data-enter-course]').disabled=true;root.querySelector('[data-outro-hint]').textContent='沙粒落尽 · 即将进入课程';queue();}
    function stop(){endOrbit();active=false;previous=0;cancelAnimationFrame(raf);raf=0;}
    function needsFrames(){const target=effective();return (!outro&&narration.needsFrames)||(outro&&(outro.phase!=='hold'||!reduce))||orbit.pointer!==null||Math.abs(orbit.pitch-orbit.targetPitch)+Math.abs(orbit.yaw-orbit.targetYaw)>.0001||Math.abs(captionOpacity-(caption.classList.contains('is-visible')?1:0))>.001||sequence||(!reduce&&settings.backgroundEnabled&&captionOpacity>.001)||target.wander>0||visual.camera>0||visual.radiation>0||Math.abs(visual.spin)>.00001||cameraBridge!==null||Object.keys(visual).some(key=>Math.abs(visual[key]-target[key])>.0001);}
    function queue(){if(!raf&&active&&dialog.open&&!document.hidden&&needsFrames())raf=requestAnimationFrame(tick);}
    function tick(now){
      raf=0;if(!active||!dialog.open||document.hidden)return;
      const dt=previous?Math.min(100,now-previous):0;previous=now;time+=dt/1000;
      const target=effective(),blend=1-Math.exp(-dt/460);
      for(const key of Object.keys(visual)){visual[key]+=(target[key]-visual[key])*blend;if(Math.abs(visual[key]-target[key])<.0001)visual[key]=target[key];}
      const damping=1-Math.exp(-cameraRig.manual.responsePerSecond*dt/1000);
      orbit.pitch+=(orbit.targetPitch-orbit.pitch)*damping;orbit.yaw+=(orbit.targetYaw-orbit.yaw)*damping;
      if(!outro&&orbit.pointer===null){
        spinAngle+=dt/1000*visual.spin*timeline.state().direction;
        if(cameraBridge){cameraBridge.elapsed+=dt;if(cameraBridge.elapsed>=cameraBridge.duration)cameraBridge=null;}
      }
      if(outro){advanceOutro(dt);if(!active)return;}
      if(!outro&&sequence&&orbit.pointer===null&&!window.CourseOpeningVoice?.holdsScene()){
        if(entrance){elapsed+=dt;progress=Math.max(0,Math.min(1,(elapsed-entranceHold)/entranceDuration));if(progress===1){entrance=false;entrancePose=null;pair='intro';syncTimeline(timeline.state());}}
        else syncTimeline(timeline.advance(dt));
      }
      const captionTarget=caption.classList.contains('is-visible')?1:0;captionOpacity+=(captionTarget-captionOpacity)*(1-Math.exp(-dt/(settings.textFade*1000/3)));
      if(!outro){
        narration.setScene(scene,timeline.state().cycles);
        window.CourseOpeningVoice?.scene(scene,captionTarget===1&&!entrance,timeline.state().direction,timeline.state().cycles,narration.language==='en');
        narration.tick(dt,captionTarget===1&&!entrance,{fadeMs:reduce?0:settings.textFade*1000,holdEnglish:Boolean(window.CourseOpeningVoice?.holdsScene())});
      }
      draw();queue();if(!raf)previous=0;
    }
    function entrancePositions(){
      // Area-uniform loose sand in a disk. Its same particle IDs flow into the
      // first rope figure; the disk remains visible before the slow formation.
      const disk=new Float32Array(N*3);
      for(let i=0;i<N;i++){const g=i*4,radialSeed=(grains[g]*17.31+grains[g+2]*31.73)%1,angleSeed=(grains[g+1]*13.17+grains[g+3]*7.29)%1,r=.88*Math.sqrt(radialSeed),theta=angleSeed*Math.PI*2;disk[i*3]=r*Math.cos(theta);disk[i*3+1]=r*Math.sin(theta);disk[i*3+2]=(grains[g+2]-.5)*.006;}
      return disk;
    }
    const diskNormals=new Float32Array(N*3);for(let i=0;i<N;i++)diskNormals[i*3+2]=1;
    function play(){
      stop();narration.reset();outro=null;delete root.dataset.outro;panel.querySelector('[data-enter-course]').disabled=false;rebuildDurations();const first=order[0];spinAngle=0;routeOffset=0;cameraBridge=null;entrancePose=null;entranceDuration=transitions[0];timeline.seek(0);timeline.setDirection(1);destination=targets[first];source=reduce?targets[first]:entrancePositions();normalSource=reduce?normals[first]:diskNormals;normalDestination=normals[first];extrusionFrom=reduce&&first<5?1:0;extrusionTo=first<5?1:0;orbit.pitch=orbit.yaw=orbit.targetPitch=orbit.targetYaw=0;pair=reduce?first+':'+first:'intro';scene=first;progress=reduce?1:0;moving=!reduce;entrance=!reduce;elapsed=0;time=0;sequence=!reduce;active=true;captionOpacity=reduce?1:0;
      for(const key of Object.keys(visual))visual[key]=0;
      upload();updateCaption();draw();showCaption(reduce);queue();
    }
    function direction(value){
      if(entrance){timeline.setDirection(value,false);root.dataset.direction=String(value);return;}
      syncTimeline(timeline.setDirection(value,false));sequence=true;active=true;draw();queue();
    }
    function refresh(){if(!outro)rebuildDurations();if(!settings.depthEnabled){endOrbit();orbit.targetPitch=orbit.targetYaw=0;}draw();queue();}
    let observer;
    function onVisibility(){previous=0;if(document.hidden){cancelAnimationFrame(raf);raf=0;}else queue();}
    film={play,stop,refresh,direction,outro:beginOutro,depart,outroReady:()=>outro?.phase==='hold',resetPolyhedra(){geometry.resetPolyhedra();upload();},dispose(){stop();lettering.dispose();if(observer)observer.disconnect();document.removeEventListener('visibilitychange',onVisibility);root.removeEventListener('pointerdown',beginOrbit);root.removeEventListener('pointermove',moveOrbit);for(const name of ['pointerup','pointercancel','lostpointercapture'])root.removeEventListener(name,endOrbit);}};
    root._openingPreview={
      show(index){const slot=order.indexOf(index);if(slot<0)throw new RangeError('Figure is not selected');stop();entrance=false;sequence=false;active=true;pair='preview';syncTimeline(timeline.seek(starts[slot]+holds[slot]/2));draw();queue();},
      transition(index,value){stop();normalSource=snapshotNormals();source=snapshot(false,time,false);extrusionFrom=0;extrusionTo=index<5?1:0;destination=targets[index];normalDestination=normals[index];scene=index;pair='manual';progress=value;moving=true;entrance=false;sequence=false;active=true;upload();updateCaption();showCaption(false);draw();queue();},
      settings(value){Object.assign(settings,value);updateSettings();},
      atTime(value){time=value;Object.assign(visual,{camera:effective().camera,background:effective().background,radiation:effective().radiation,spin:effective().spin});spinAngle=value*visual.spin;draw();},
      seek(value){entrance=false;sequence=false;active=true;syncTimeline(timeline.seek(value));draw();},
      advance(value){entrance=false;syncTimeline(timeline.advance(value));draw();},
      direction(value,engage=false){syncTimeline(timeline.setDirection(value,engage));draw();},
      evidence(){return{outro:outro?{phase:outro.phase,elapsed:outro.elapsed,view:outro.view}:null,count:N,stride:3,scene,progress,time,entrance,entranceElapsed:elapsed,positions:snapshot(),visiblePositions:snapshot(true),targets,settings:{...settings},effective:effective(),rendered:{...visual},camera:cameraPose(),orbit:{...orbit},spinAngle,spinVelocity:visual.spin,routeOffset,cameraBridge:cameraBridge?{elapsed:cameraBridge.elapsed,duration:cameraBridge.duration}:null,order:[...order],holds:[...holds],transitions:[...transitions],cameraRig:cameraRig.evidence(),timeline:timeline.state(),duration:timeline.duration,starts,geometry:geometry.evidence(),glError:gl.getError()};}
    };
    document.addEventListener('visibilitychange',onVisibility);observer=new ResizeObserver(draw);observer.observe(canvas);
    boot.advance(95,'准备呈现');updateCaption();draw();await paint();root.dataset.particleCount=String(N);root.dataset.ready='true';boot.advance(100,'准备完成');await paint();
  }
  if(!location.hash&&!window.courseOpeningDismissed)openOpening();
  else document.documentElement.classList.remove('course-opening-pending');
})();
