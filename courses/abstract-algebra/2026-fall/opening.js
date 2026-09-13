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
  // thirty-second dwell preference; morphs are additional time.
  const storageKey = 'courseOpeningAppearance.v3';
  const durationChoices = [30,45,60,90];
  const morphSpeedChoices=[.25,.5,.75,1,1.5],spinSpeedScale=2;
  const defaults = Object.freeze({backgroundBrightness:160,gemPercent:1.5,titleScale:115,quoteScale:115,textFade:2.4,complexityEnabled:true,complexityAmount:.5,depthEnabled:true,wanderEnabled:true,wanderAmount:.22,cameraEnabled:true,backgroundEnabled:true,radiationEnabled:true,radiationAmount:.45,radiationFineOnly:true,grainTypes:Object.freeze([true,true,true,true,true,true]),morphSpeed:.5,galoisScoreEnabled:true,shuffleScenes:false,spotlightEnabled:true,spinEnabled:true,spinSpeed:.6,sceneDurations:Object.freeze([30,30,30,30,30,30,30,30,30,30]),sceneEnabled:Object.freeze([false,false,false,true,true,true,true,true,true,true])});
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
  function effective() {return {complexity:settings.complexityEnabled?settings.complexityAmount:0,depth:settings.depthEnabled?1:0,wander:settings.wanderEnabled?settings.wanderAmount:0,camera:!['outro','departing'].includes(stage)&&settings.cameraEnabled?1:0,background:settings.backgroundEnabled?1:0,spotlight:settings.spotlightEnabled?1:0,radiation:!['outro','departing'].includes(stage)&&settings.radiationEnabled?settings.radiationAmount:0,spin:!['outro','departing'].includes(stage)&&settings.spinEnabled?settings.spinSpeed*spinSpeedScale*Math.PI/180:0};}
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
    panel.querySelector('[data-playback-order]').value=settings.shuffleScenes?'random':'sequential';
    const spinInput=panel.querySelector('[data-spin-speed]');spinInput.value=String(settings.spinSpeed*spinSpeedScale);spinInput.disabled=!settings.spinEnabled;
    spinInput.style.setProperty('--range-progress',(settings.spinSpeed/3*100)+'%');panel.querySelector('[data-spin-output]').textContent=(settings.spinSpeed*spinSpeedScale).toFixed(1)+'°/秒';
    panel.querySelectorAll('[data-scene-duration]').forEach(input=>{input.value=String(settings.sceneDurations[Number(input.dataset.sceneDuration)]);input.disabled=input.dataset.sceneDuration==='9'&&settings.galoisScoreEnabled;});
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
    else if(input.hasAttribute('data-spin-speed')&&Number.isFinite(Number(input.value)))settings.spinSpeed=Math.max(0,Math.min(3,Number(input.value)/spinSpeedScale));
    else if(input.hasAttribute('data-playback-order'))settings.shuffleScenes=input.value==='random';
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
    if((event.key===' '||event.key==='Enter')&&!event.repeat&&!panel.contains(event.target)){
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
    const story=window.CourseOpeningGaloisStory;
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
    const narration=window.CourseOpeningNarration.create(quote,[...backdrop.scenes,...story.nodes,story.recognition]);
    const letterLoc={pos:gl.getAttribLocation(letterProgram,'pos'),visibility:gl.getUniformLocation(letterProgram,'visibility'),texture:gl.getUniformLocation(letterProgram,'lettering'),sweepTime:gl.getUniformLocation(letterProgram,'sweepTime'),sweepEnabled:gl.getUniformLocation(letterProgram,'sweepEnabled')};
    let captionOpacity=0;const impulses=window.CourseOpeningImpulse.create();let clickCandidate=null;
    const quad = buffer(new Float32Array([-1,-1,1,-1,-1,1,-1,1,1,-1,1,1]), gl.STATIC_DRAW);
    const selectedScenes=()=>settings.sceneEnabled.flatMap((on,i)=>i>=3&&on?[i]:[]);
    const playlistSeed=(Math.random()*4294967296)>>>0,motion=window.CourseOpeningMotion.create();
    let playlist=window.CourseOpeningPlaylist.create({sceneIds:selectedScenes(),randomized:settings.shuffleScenes,seed:playlistSeed}),routeCycle=0;
    const initialScene=playlist.order(0)[0];
    let source=targets[initialScene],destination=targets[initialScene],normalSource=normals[initialScene],normalDestination=normals[initialScene],extrusionFrom=initialScene<5?1:0,extrusionTo=extrusionFrom;
    let twoSidedFrom=initialScene===7?1:0,twoSidedTo=twoSidedFrom;
    const sourceBuffer=buffer(source,gl.DYNAMIC_DRAW),destinationBuffer=buffer(destination,gl.DYNAMIC_DRAW);
    const normalSourceBuffer=buffer(normalSource,gl.DYNAMIC_DRAW),normalDestinationBuffer=buffer(normalDestination,gl.DYNAMIC_DRAW);
    let seed=317129;const grains=new Float32Array(N*4);
    for(let i=0;i<grains.length;i++){seed=(Math.imul(seed,1664525)+1013904223)>>>0;grains[i]=seed/4294967296;}
    const grainBuffer=buffer(grains,gl.STATIC_DRAW);
    const loc={source:gl.getAttribLocation(program,'start'),destination:gl.getAttribLocation(program,'finish'),normalSource:gl.getAttribLocation(program,'normalStart'),normalDestination:gl.getAttribLocation(program,'normalFinish'),grain:gl.getAttribLocation(program,'grain'),quad:gl.getAttribLocation(background,'pos')};
    for(const name of ['galoisLossFrom','galoisLossTo','galoisFit','narrativeLight','progress','aspect','dpr','time','gemShare','outroFall','outroExit','complexity','depth','wander','camera','radiation','viewAngles','viewTarget','viewZoom','spotlight','objectSpin','extrusionFrom','extrusionTo','twoSided','radiationFineOnly','grainTypes[0]','impulses[0]','impulseRadii[0]'])loc[name]=gl.getUniformLocation(program,name);
    const bgLoc={};for(const name of ['time','aspect','camera','background','stageLight','spotlight','viewAngles','viewTarget','viewZoom'])bgLoc[name]=gl.getUniformLocation(background,name);
    function attribute(data,location,size){gl.bindBuffer(gl.ARRAY_BUFFER,data);gl.enableVertexAttribArray(location);gl.vertexAttribPointer(location,size,gl.FLOAT,false,0,0);}
    const baseTransitions=[4200,4200,4200,5200,5400,5000,5000,5000,5000,5000],entranceHold=0;
    let order=playlist.order(0);
    let storyHoldMs=settings.sceneDurations[9]*1000,storyMorphMs=baseTransitions[9]/settings.morphSpeed,storyScored=settings.galoisScoreEnabled;
    const transitionTimes=(ids,deck=playlist,cycle=routeCycle)=>ids.map((id,i)=>{
      const to=i+1<ids.length?ids[i+1]:deck.order(cycle+1)[0];
      return baseTransitions[id]/settings.morphSpeed*((id===9||to===9)?cameraRig.portraitTransitionScale:1);
    });
    const holdTimes=(ids,hold=storyHoldMs,morph=storyMorphMs,scored=storyScored)=>ids.map(id=>id===9?story.duration(hold,morph,scored):settings.sceneDurations[id]*1000);
    let transitions=transitionTimes(order);
    let holds=holdTimes(order);
    let timeline=window.CourseOpeningTimeline.create({holds,transitions,morphSingle:order.length===1&&order[0]===9});
    const makeStarts=()=>holds.map((_,i)=>holds.slice(0,i).reduce((sum,x,j)=>sum+x+transitions[j],0));
    let starts=makeStarts();
    let scene=initialScene,progress=1,moving=false,active=false,sequence=false,entrance=false,elapsed=0,time=0,previous=0,raf=0,pair=initialScene+':'+initialScene;
    const visual={camera:0,background:0,spotlight:0,radiation:0,spin:0};
    let outro=null,galoisState=null,galoisNode=0,displayedGaloisNode=-1;
    let spinAngle=0,routeOffset=0,cameraBridge=null,entrancePose=null,entranceDuration=transitions[0];
    let entranceViewport=null;
    let entrancePortraitWeight=initialScene===9?1:0,manualPortraitWeight=0;
    let entranceGroupWeight=[6,7].includes(initialScene)?1:0,manualGroupWeight=0;
    const orbit={pitch:0,yaw:0,targetPitch:0,targetYaw:0,pointer:null,solid:-1,x:0,y:0};
    const ease=t=>t*t*t*(t*(t*6-15)+10);
    function mappedState(state=timeline.state()){
      const from=order[state.from],to=state.moving&&state.from===order.length-1&&state.to===0?playlist.order(state.cycles+1)[0]:order[state.to];
      return {...state,from,to,scene:state.moving?to:order[state.scene]};
    }
    function syncCycle(state){
      if(state.cycles===routeCycle)return state;
      const oldDuration=timeline.duration,previousCycle=routeCycle;
      routeCycle=state.cycles;order=playlist.order(routeCycle);
      transitions=transitionTimes(order);holds=holdTimes(order);starts=makeStarts();
      timeline=window.CourseOpeningTimeline.create({holds,transitions,morphSingle:order.length===1&&order[0]===9});timeline.setDirection(state.direction);
      const position=state.cycles<previousCycle?timeline.duration-(oldDuration-state.position):state.position;
      return timeline.seek(state.cycles*timeline.duration+position);
    }
    function spinDirection(){return motion.sceneDirection(entrance||pair==='manual'?{scene,moving:false}:mappedState());}
    function advanceObjectSpins(angle){
      let changed=false;
      for(const id of [6,7])if(source===targets[id]||destination===targets[id]){
        for(const step of motion.objectSteps(id,angle)){
          if(id===6)geometry.rotatePolyhedron(step.index,step.axis,step.angle);
          else geometry.rotateTopology(step.index,step.axis,step.angle);
        }
        changed=true;
      }
      if(changed)upload();
    }
    function portraitWeight(){
      if(outro)return 0;
      if(entrance||pair==='manual'){
        const from=entrance?entrancePortraitWeight:manualPortraitWeight,to=scene===9?1:0;
        return from+(to-from)*Math.max(0,Math.min(1,ease(Math.min(1,progress))));
      }
      const state=timeline.state();
      return cameraRig.portraitWeight(mappedState(state));
    }
    function groupWeight(){
      if(outro)return 0;
      if(entrance||pair==='manual'){
        const from=entrance?entranceGroupWeight:manualGroupWeight,to=[6,7].includes(scene)?1:0;
        const duration=entrance?entranceDuration:transitions[order.indexOf(scene)];
        return from+(to-from)*Math.max(0,Math.min(1,ease(Math.min(1,progress*duration/cameraRig.groupReturnMs))));
      }
      const state=timeline.state();
      return cameraRig.groupWeight(mappedState(state),transitions[state.from]);
    }
    function twoSidedWeight(){return twoSidedFrom+(twoSidedTo-twoSidedFrom)*Math.max(0,Math.min(1,ease(progress)));}
    function renderedSpin(){return spinAngle*(1-portraitWeight());}
    function storyTreatment(){
      if(!storyScored||!galoisState||entrance||outro||pair==='manual')return {from:0,to:0,light:1};
      const t=timeline.state().holdElapsed,state=galoisState,loss=ease(Math.max(0,Math.min(1,(t-124550)/2450)));
      const shades=[1,.94,1.04,.68,.86,.70,1.03],q=state.moving?ease(state.progress):0;
      let light=shades[state.from]+(shades[state.to]-shades[state.from])*q;
      if(state.node===6&&!state.moving)light+=.12*Math.exp(-Math.pow((t-166150)/3200,2));
      return {from:state.from===5?loss:0,to:state.to===5?loss:0,light};
    }
    function galoisFit(){const rect=canvas.getBoundingClientRect();return rect.width<700&&rect.height<700?[.66,-.34]:[1,0];}
    function snapshot(withEffects=false,atTime=time,world=true){
      const treatment=storyTreatment(),fit=galoisFit(),e=ease(progress),arch=Math.sin(Math.PI*e),result=new Float32Array(N*3),appearance=effective(),cosine=Math.cos(renderedSpin()),sine=Math.sin(renderedSpin());
      for(let i=0;i<N;i++){
        const k=i*3,g=i*4,a=treatment.from?materials.storyLoss(source.subarray(k,k+3),treatment.from,grains[g],fit).point:source.subarray(k,k+3),b=treatment.to?materials.storyLoss(destination.subarray(k,k+3),treatment.to,grains[g],fit).point:destination.subarray(k,k+3);
        const dx=b[0]-a[0],dy=b[1]-a[1],drift=arch*Math.min(.022,Math.hypot(dx,dy)*.16);
        let x=a[0]+dx*e-dy*arch*.28+Math.sin(grains[g]*19+e*6.283)*drift;
        let y=a[1]+dy*e+dx*arch*.28+Math.cos(grains[g+1]*23-e*6.283)*drift;
        const fromZ=a[2]*(1-extrusionFrom+extrusionFrom*appearance.depth),toZ=b[2]*(1-extrusionTo+extrusionTo*appearance.depth);
        let z=fromZ+(toZ-fromZ)*e;
        if(withEffects){
          const normal=[0,0,0];
          for(let axis=0;axis<3;axis++){const face=axis===2?1:0,a=normalSource[k+axis]+(face-normalSource[k+axis])*extrusionFrom*(1-appearance.depth),b=normalDestination[k+axis]+(face-normalDestination[k+axis])*extrusionTo*(1-appearance.depth);normal[axis]=a+(b-a)*e;}
          const escaped=materials.radiationOffset(x,y,z,grains[g],grains[g+1],grains[g+2],grains[g+3],atTime,visual.radiation,normal,settings.radiationFineOnly);
          const d=materials.localOffset(x,y,grains[g],grains[g+1],grains[g+2],grains[g+3],atTime,appearance.wander);
          x+=d[0]*(1-escaped.chosen)+escaped.offset[0];y+=d[1]*(1-escaped.chosen)+escaped.offset[1];z+=escaped.offset[2];
          if(impulses.active(atTime)){const impulse=impulses.offset([x,y,z],atTime,grains[g]);x+=impulse[0];y+=impulse[1];z+=impulse[2];}
        }
        result[k]=world?x*cosine-y*sine:x;result[k+1]=world?x*sine+y*cosine:y;result[k+2]=z;
      }return result;
    }
    function snapshotNormals(){const e=ease(progress),out=new Float32Array(N*3),flat=1-effective().depth;for(let i=0;i<out.length;i++){const face=i%3===2?1:0,a=normalSource[i]+(face-normalSource[i])*extrusionFrom*flat,b=normalDestination[i]+(face-normalDestination[i])*extrusionTo*flat;out[i]=a+(b-a)*e;}return out;}
    function upload(){for(const [buf,data] of [[sourceBuffer,source],[destinationBuffer,destination],[normalSourceBuffer,normalSource],[normalDestinationBuffer,normalDestination]]){gl.bindBuffer(gl.ARRAY_BUFFER,buf);gl.bufferSubData(gl.ARRAY_BUFFER,0,data);}}
    function textFadeMs(){return (scene===9&&storyScored?Math.min(1.1,settings.textFade):settings.textFade)*1000;}
    function narrationIndex(){return scene===9?backdrop.scenes.length+(galoisNode===6&&(!storyScored||timeline.state().holdElapsed>=166000)?story.nodes.length:galoisNode):scene;}
    function updateCaption(){
      const node=scene===9?story.nodes[galoisNode]:null,text=node?{title:node.title,zh:node.zhTitle,en:node.en}:geometry.captions[scene];
      for(const field of ['title','zh'])root.querySelector('[data-caption-'+field+']').textContent=text[field];
      root.querySelector('[data-caption-year]').textContent=node?node.year:'';
      root.classList.toggle('is-galois-story',scene===9);displayedGaloisNode=scene===9?galoisNode:-1;
      narration.setScene(narrationIndex(),timeline.state().cycles);quote.classList.remove('is-visible');
      canvas.setAttribute('aria-label',text.title+'。'+text.zh+'。'+text.en);
      root.querySelectorAll('[data-drag-hint]').forEach(el=>el.textContent=scene===9?'正面展示':scene===7?'分别拖动圆与 Möbius 带':scene===6?'分别拖动五个多面体':'拖动旋转');
    }
    function syncTimeline(state){
      state=syncCycle(state);const mapped=mappedState(state),{from,to}=mapped;
      galoisState=!state.moving&&mapped.scene===9?story.state(state.holdElapsed,storyHoldMs,storyMorphMs,storyScored):null;
      const local=galoisState||state,fromNode=state.moving?story.nodes.length-1:local.from,toNode=state.moving?0:local.to;
      const key=from+':'+to+':'+(from===9?fromNode:'')+':'+(to===9?toNode:'');
      if(key!==pair){
        pair=key;source=from===9?geometry.galoisNode(fromNode).positions:targets[from];destination=to===9?geometry.galoisNode(toNode).positions:targets[to];
        normalSource=from===9?geometry.galoisNode(fromNode).normals:normals[from];normalDestination=to===9?geometry.galoisNode(toNode).normals:normals[to];
        extrusionFrom=from<5?1:0;extrusionTo=to<5?1:0;twoSidedFrom=from===7?1:0;twoSidedTo=to===7?1:0;upload();
      }
      progress=local.progress;moving=local.moving;
      const label=state.moving?(state.direction>0?to:from):order[state.scene];
      if(galoisState)galoisNode=galoisState.node;
      if(!moving&&(scene!==label||(label===9&&displayedGaloisNode!==galoisNode))){scene=label;updateCaption();}
      const spent=state.direction>0?local.holdElapsed:local.holdDuration-local.holdElapsed;
      const remaining=state.direction>0?local.holdDuration-local.holdElapsed:local.holdElapsed;
      showCaption(!moving&&spent>420&&remaining>textFadeMs()+100);
      root.dataset.galoisNode=String(galoisNode);
    }
    function baseCameraPose(){
      const state=timeline.state(),mapped=mappedState(state);
      const pose=cameraRig.sampleTimeline(mapped,{holds,transitions,starts,duration:timeline.duration,phaseOffset:routeOffset,sceneIds:order});
      if(entrance)return cameraRig.blend(entrancePose||{angles:[0,0,0],zoom:1,target:[0,0,0]},pose,ease(progress));
      return cameraBridge?cameraRig.blend(cameraBridge.from,pose,ease(cameraBridge.elapsed/cameraBridge.duration)):pose;
    }
    function cameraPose(){
      if(outro)return outro.view;
      const state=timeline.state(),pose=baseCameraPose();
      let target=pose.target.map(value=>value*visual.camera);
      if(!settings.depthEnabled&&!state.moving&&order[state.scene]<5)target[2]=0;
      target=materials.rotateObject(target,renderedSpin());
      const view=cameraRig.frameGroup({angles:[pose.angles[0]*visual.camera+orbit.pitch,pose.angles[1]*visual.camera+orbit.yaw,pose.angles[2]*visual.camera],target,zoom:Math.max(1,1+(pose.zoom-1)*visual.camera),perspective:Math.max(visual.camera,settings.depthEnabled?1:0)},groupWeight());
      const weight=portraitWeight();
      return {...cameraRig.blend(view,{angles:[0,0,0],target:[0,0,0],zoom:1},weight),perspective:view.perspective*(1-weight)};
    }
    function rebuildDurations(){
      const nextPlaylist=window.CourseOpeningPlaylist.create({sceneIds:selectedScenes(),randomized:settings.shuffleScenes,seed:playlistSeed});
      const nextOrder=nextPlaylist.order(timeline.state().cycles),nextTransitions=transitionTimes(nextOrder,nextPlaylist,timeline.state().cycles);
      const nextStoryHold=settings.sceneDurations[9]*1000,nextStoryMorph=baseTransitions[9]/settings.morphSpeed,nextStoryScored=settings.galoisScoreEnabled;
      const next=holdTimes(nextOrder,nextStoryHold,nextStoryMorph,nextStoryScored);
      if(nextPlaylist.randomized===playlist.randomized&&nextOrder.join(':')===order.join(':')&&next.every((v,i)=>v===holds[i])&&nextTransitions.every((v,i)=>v===transitions[i]))return;
      const previousPortraitWeight=portraitWeight(),previousGroupWeight=groupWeight(),previousPose=baseCameraPose(),old=timeline.state(),oldPhase=old.position/timeline.duration+routeOffset;
      const oldMapped=mappedState(old),oldFrom=oldMapped.from,oldTo=oldMapped.to,oldScene=oldMapped.scene;
      const captured=snapshot(false,time,false),capturedNormals=snapshotNormals(),capturedTwoSided=twoSidedWeight();
      const retainedEntrance=entrance&&nextOrder.includes(scene);
      const preservedStory=oldScene===9&&!old.moving?story.remap(old.holdElapsed,storyHoldMs,storyMorphMs,nextStoryHold,nextStoryMorph,storyScored,nextStoryScored):null;
      playlist=nextPlaylist;routeCycle=old.cycles;order=nextOrder;holds=next;transitions=nextTransitions;starts=makeStarts();storyHoldMs=nextStoryHold;storyMorphMs=nextStoryMorph;storyScored=nextStoryScored;
      timeline=window.CourseOpeningTimeline.create({holds,transitions,morphSingle:order.length===1&&order[0]===9});timeline.setDirection(old.direction);
      const fromSlot=order.indexOf(oldFrom),toSlot=order.indexOf(oldTo),sceneSlot=order.indexOf(oldScene);
      const retainedMorph=!entrance&&old.moving&&order.length>1&&fromSlot>=0&&(fromSlot===order.length-1?oldTo===playlist.order(routeCycle+1)[0]:toSlot===fromSlot+1);
      let needsFormation=false,position=0;
      if(retainedEntrance)position=starts[order.indexOf(scene)];
      else if(retainedMorph)position=starts[fromSlot]+holds[fromSlot]+old.progress*transitions[fromSlot];
      else if(!entrance&&!old.moving&&sceneSlot>=0)position=starts[sceneSlot]+(preservedStory!==null?preservedStory:old.holdElapsed/old.holdDuration*(order.length===1?timeline.duration:holds[sceneSlot]));
      else{const targetSlot=order.includes(scene)?order.indexOf(scene):0;position=starts[targetSlot];needsFormation=true;}
      timeline.seek(position+old.cycles*timeline.duration);
      routeOffset=oldPhase-timeline.state().position/timeline.duration;routeOffset-=Math.floor(routeOffset);cameraBridge=null;
      if(retainedEntrance){entranceDuration=pair==='intro'?Math.min(4200,transitions[order.indexOf(scene)]):transitions[order.indexOf(scene)];if(elapsed>entranceHold)elapsed=entranceHold+progress*entranceDuration;}
      else if(needsFormation&&!reduce){
        scene=order[timeline.state().scene];source=captured;normalSource=capturedNormals;destination=targets[scene];normalDestination=normals[scene];
        extrusionFrom=0;extrusionTo=scene<5?1:0;twoSidedFrom=capturedTwoSided;twoSidedTo=scene===7?1:0;pair='selection';progress=0;moving=true;entrance=true;entrancePose=previousPose;entrancePortraitWeight=previousPortraitWeight;entranceGroupWeight=previousGroupWeight;
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
      if(stage!=='playing'||portraitWeight()>=.999||!settings.depthEnabled||event.button!==0||!event.isPrimary||panel.contains(event.target)||event.target.closest('button,a,input,select,summary'))return;
      orbit.solid=-1;
      if(scene===6||scene===7){
        if(entrance||moving)return;
        const rect=canvas.getBoundingClientRect(),ray=window.CourseOpeningPolyhedra.screenRay(event.clientX-rect.left,event.clientY-rect.top,rect.width,rect.height,cameraPose(),renderedSpin());
        orbit.solid=scene===7?geometry.pickTopology(ray):geometry.pickPolyhedron(ray);if(orbit.solid<0)return;root.dataset.draggingSolid=String(orbit.solid);
      }
      orbit.pointer=event.pointerId;orbit.x=event.clientX;orbit.y=event.clientY;
      root.setPointerCapture(event.pointerId);root.classList.add('is-orbiting');event.preventDefault();queue();
    }
    function moveOrbit(event){
      if(event.pointerId!==orbit.pointer)return;
      if(orbit.solid>=0){
        const rotation=window.CourseOpeningPolyhedra.dragRotation(event.clientX-orbit.x,event.clientY-orbit.y,cameraPose(),renderedSpin());
        if(scene===7)geometry.rotateTopology(orbit.solid,rotation.axis,rotation.angle);else geometry.rotatePolyhedron(orbit.solid,rotation.axis,rotation.angle);upload();
        orbit.x=event.clientX;orbit.y=event.clientY;event.preventDefault();draw();queue();return;
      }
      const control=cameraRig.manual;
      orbit.targetYaw+=(event.clientX-orbit.x)*control.yawPerPixel;
      orbit.targetPitch=Math.max(-control.pitchLimit,Math.min(control.pitchLimit,orbit.targetPitch+(event.clientY-orbit.y)*control.pitchPerPixel));
      orbit.x=event.clientX;orbit.y=event.clientY;event.preventDefault();queue();
    }
    function startClick(event){
      if(stage!=='playing'||event.button!==0||!event.isPrimary||panel.contains(event.target)||event.target.closest('button,a,input,select,summary'))return;
      clickCandidate={id:event.pointerId,x:event.clientX,y:event.clientY,moved:false};
    }
    function moveClick(event){if(clickCandidate?.id===event.pointerId&&Math.hypot(event.clientX-clickCandidate.x,event.clientY-clickCandidate.y)>6)clickCandidate.moved=true;}
    function cancelClick(){clickCandidate=null;}
    function releaseClick(event){
      const candidate=clickCandidate;clickCandidate=null;
      if(!candidate||candidate.id!==event.pointerId||candidate.moved||Math.hypot(event.clientX-candidate.x,event.clientY-candidate.y)>6||stage!=='playing'||panel.contains(event.target)||event.target.closest('button,a,input,select,summary'))return;
      const rect=canvas.getBoundingClientRect(),x=event.clientX-rect.left,y=event.clientY-rect.top;
      if(x<0||y<0||x>rect.width||y>rect.height)return;
      const hit=window.CourseOpeningImpulse.fromScreen(x,y,rect.width,rect.height,cameraPose(),renderedSpin());
      impulses.trigger(hit.origin,hit.radius,time);active=true;draw();queue();
    }
    root.addEventListener('pointerdown',startClick);root.addEventListener('pointermove',moveClick);root.addEventListener('pointerup',releaseClick);
    root.addEventListener('pointercancel',cancelClick);root.addEventListener('lostpointercapture',cancelClick);
    root.addEventListener('pointerdown',beginOrbit);root.addEventListener('pointermove',moveOrbit);
    root.addEventListener('pointerup',endOrbit);root.addEventListener('pointercancel',endOrbit);root.addEventListener('lostpointercapture',endOrbit);
    function draw(){
      if(!dialog.open)return;
      const rect=canvas.getBoundingClientRect(),ratio=Math.min(2,window.devicePixelRatio||1),width=Math.max(1,Math.round(rect.width*ratio)),height=Math.max(1,Math.round(rect.height*ratio));
      if(entrance&&pair==='intro'&&(!entranceViewport||entranceViewport[0]!==rect.width||entranceViewport[1]!==rect.height)){source=entrancePositions(rect);upload();}
      if(geometry.fitGalois(rect.width<700&&rect.height<700))upload();
      if(canvas.width!==width||canvas.height!==height){canvas.width=width;canvas.height=height;}
      const view=cameraPose();
      lettering.update(scene,rect.width,rect.height,ratio);
      gl.viewport(0,0,width,height);gl.disable(gl.DEPTH_TEST);gl.depthMask(false);gl.disable(gl.BLEND);gl.useProgram(background);
      gl.uniform1f(bgLoc.time,time);gl.uniform1f(bgLoc.aspect,width/height);gl.uniform1f(bgLoc.camera,0);gl.uniform3fv(bgLoc.viewAngles,[0,0,0]);gl.uniform3fv(bgLoc.viewTarget,[0,0,0]);gl.uniform1f(bgLoc.viewZoom,1);gl.uniform1f(bgLoc.background,visual.background);gl.uniform1f(bgLoc.stageLight,settings.backgroundBrightness/100);gl.uniform1f(bgLoc.spotlight,visual.spotlight);
      attribute(quad,loc.quad,2);gl.drawArrays(gl.TRIANGLES,0,6);
      gl.useProgram(letterProgram);attribute(quad,letterLoc.pos,2);lettering.bind();gl.uniform1i(letterLoc.texture,0);gl.uniform1f(letterLoc.visibility,captionOpacity);gl.uniform1f(letterLoc.sweepTime,time%24);gl.uniform1f(letterLoc.sweepEnabled,!reduce&&settings.backgroundEnabled?1:0);gl.enable(gl.BLEND);gl.blendFunc(gl.SRC_ALPHA,gl.ONE_MINUS_SRC_ALPHA);gl.drawArrays(gl.TRIANGLES,0,6);
      gl.depthMask(true);gl.clearDepth(1);gl.clear(gl.DEPTH_BUFFER_BIT);gl.enable(gl.DEPTH_TEST);gl.depthFunc(gl.LEQUAL);
      gl.useProgram(program);attribute(sourceBuffer,loc.source,3);attribute(destinationBuffer,loc.destination,3);attribute(normalSourceBuffer,loc.normalSource,3);attribute(normalDestinationBuffer,loc.normalDestination,3);attribute(grainBuffer,loc.grain,4);
      gl.enable(gl.BLEND);gl.blendFunc(gl.SRC_ALPHA,gl.ONE_MINUS_SRC_ALPHA);
      const impulseUniforms=impulses.uniforms();gl.uniform4fv(loc['impulses[0]'],impulseUniforms.values);gl.uniform1fv(loc['impulseRadii[0]'],impulseUniforms.radii);
      const treatment=storyTreatment();gl.uniform1f(loc.galoisLossFrom,treatment.from);gl.uniform1f(loc.galoisLossTo,treatment.to);gl.uniform2fv(loc.galoisFit,galoisFit());gl.uniform1f(loc.narrativeLight,treatment.light);
      gl.uniform1f(loc.progress,progress);gl.uniform1f(loc.aspect,width/height);gl.uniform1f(loc.dpr,ratio*Math.max(1,Math.min(1.4,rect.height/800)));gl.uniform1f(loc.time,time);
      const appearance=effective();for(const name of ['complexity','depth','wander'])gl.uniform1f(loc[name],appearance[name]);gl.uniform1f(loc.camera,view.perspective);gl.uniform3fv(loc.viewAngles,view.angles);gl.uniform3fv(loc.viewTarget,view.target);gl.uniform1f(loc.viewZoom,view.zoom);gl.uniform1f(loc.objectSpin,renderedSpin());gl.uniform1f(loc.spotlight,visual.spotlight);gl.uniform1f(loc.twoSided,twoSidedWeight());gl.uniform1f(loc.extrusionFrom,extrusionFrom);gl.uniform1f(loc.extrusionTo,extrusionTo);gl.uniform1f(loc.radiation,visual.radiation);gl.uniform1f(loc.radiationFineOnly,settings.radiationFineOnly?1:0);gl.uniform1fv(loc['grainTypes[0]'],settings.grainTypes.map(Number));gl.uniform1f(loc.gemShare,settings.gemPercent/100);gl.uniform1f(loc.outroFall,outro&&!reduce?(['hold','depart'].includes(outro.phase)?1:outro.phase==='form'?Math.max(0,(progress-.75)/.25):0):0);gl.uniform1f(loc.outroExit,outro?.phase==='depart'?outro.elapsed/(reduce?170:1000):-1);
      gl.drawArrays(gl.POINTS,0,N);root.dataset.scene=String(scene);root.dataset.progress=progress.toFixed(4);root.dataset.time=time.toFixed(3);root.dataset.direction=String(timeline.state().direction);root.dataset.cycles=String(timeline.state().cycles);root.dataset.spin=renderedSpin().toFixed(6);
    }
    function beginOutro(){
      const view=cameraPose(),captured=snapshot(false,time,true),capturedNormals=snapshotNormals(),capturedTwoSided=twoSidedWeight();
      if(impulses.active(time)){for(let i=0;i<N;i++){const k=i*3,local=materials.rotateObject(captured.subarray(k,k+3),-renderedSpin()),offset=materials.rotateObject(impulses.offset(local,time,grains[i*4]),renderedSpin());for(let a=0;a<3;a++)captured[k+a]+=offset[a];}}
      impulses.clear();cancelClick();
      const cosine=Math.cos(renderedSpin()),sine=Math.sin(renderedSpin());
      for(let i=0;i<capturedNormals.length;i+=3){const x=capturedNormals[i],y=capturedNormals[i+1];capturedNormals[i]=cosine*x-sine*y;capturedNormals[i+1]=sine*x+cosine*y;}
      endOrbit();sequence=false;entrance=false;moving=false;cameraBridge=null;spinAngle=0;
      orbit.pitch=orbit.yaw=orbit.targetPitch=orbit.targetYaw=0;
      source=destination=captured;normalSource=normalDestination=capturedNormals;twoSidedFrom=twoSidedTo=capturedTwoSided;extrusionFrom=extrusionTo=0;progress=1;
      outro={phase:'return',elapsed:0,from:view,view};root.dataset.outro='return';
      root.querySelector('[data-outro-hint]').textContent='镜头归位 · 沙粒落字';
      panel.querySelector('[data-enter-course]').disabled=true;showCaption(false);upload();active=true;previous=0;queue();
    }
    function advanceOutro(dt){
      outro.elapsed+=dt;
      if(outro.phase==='depart'){if(outro.elapsed>=(reduce?800:4200))leaveOpening();return;}
      const neutral={angles:[0,0,0],target:[0,0,0],zoom:1,perspective:0};
      if(outro.phase==='return'){
        const amount=reduce?1:ease(Math.min(1,outro.elapsed/2700));
        outro.view={...cameraRig.blend(outro.from,neutral,amount),perspective:outro.from.perspective*(1-amount)};
        if(amount===1){
          outro.phase='form';outro.elapsed=0;outro.view=neutral;root.dataset.outro='form';
          destination=closingGeometry.positions;normalDestination=closingGeometry.normals;twoSidedTo=0;progress=0;upload();
          canvas.setAttribute('aria-label','Algebra Ⅰ. Sheng Meng.');
        }
      }else if(outro.phase==='form'){
        progress=reduce?1:Math.min(1,outro.elapsed/3600);
        if(progress===1){outro.phase='hold';root.dataset.outro='hold';panel.querySelector('[data-enter-course]').disabled=false;root.querySelector('[data-outro-hint]').textContent='按空格或回车，落沙后进入课程';}
      }
    }
    function depart(){outro.phase='depart';outro.elapsed=0;root.dataset.outro='depart';panel.querySelector('[data-enter-course]').disabled=true;root.querySelector('[data-outro-hint]').textContent='沙粒落尽 · 即将进入课程';queue();}
    function stop(){endOrbit();active=false;previous=0;cancelAnimationFrame(raf);raf=0;}
    function needsFrames(){const target=effective();return impulses.active(time)||(!outro&&narration.needsFrames)||(outro&&(outro.phase!=='hold'||!reduce))||orbit.pointer!==null||Math.abs(orbit.pitch-orbit.targetPitch)+Math.abs(orbit.yaw-orbit.targetYaw)>.0001||Math.abs(captionOpacity-(caption.classList.contains('is-visible')?1:0))>.001||sequence||(!reduce&&settings.backgroundEnabled&&captionOpacity>.001)||target.wander>0||visual.camera>0||(!reduce&&visual.spotlight>0)||visual.radiation>0||Math.abs(visual.spin)>.00001||cameraBridge!==null||Object.keys(visual).some(key=>Math.abs(visual[key]-target[key])>.0001);}
    function queue(){if(!raf&&active&&dialog.open&&!document.hidden&&needsFrames())raf=requestAnimationFrame(tick);}
    function tick(now){
      raf=0;if(!active||!dialog.open||document.hidden)return;
      const dt=previous?Math.min(100,now-previous):0;previous=now;time+=dt/1000;
      const target=effective(),blend=1-Math.exp(-dt/460);
      for(const key of Object.keys(visual)){visual[key]+=(target[key]-visual[key])*blend;if(Math.abs(visual[key]-target[key])<.0001)visual[key]=target[key];}
      const damping=1-Math.exp(-cameraRig.manual.responsePerSecond*dt/1000);
      orbit.pitch+=(orbit.targetPitch-orbit.pitch)*damping;orbit.yaw+=(orbit.targetYaw-orbit.yaw)*damping;
      if(!outro&&orbit.pointer===null){
        const free=1-portraitWeight();
        if(free===1)spinAngle=Math.atan2(Math.sin(spinAngle),Math.cos(spinAngle));
        const angle=dt/1000*visual.spin*timeline.state().direction*free;
        spinAngle+=angle*spinDirection();
        if(angle)advanceObjectSpins(angle);
        if(cameraBridge){cameraBridge.elapsed+=dt;if(cameraBridge.elapsed>=cameraBridge.duration)cameraBridge=null;}
      }
      if(outro){advanceOutro(dt);if(!active)return;}
      if(!outro&&sequence&&orbit.pointer===null&&!window.CourseOpeningVoice?.holdsScene()){
        if(entrance){elapsed+=dt;progress=Math.max(0,Math.min(1,(elapsed-entranceHold)/entranceDuration));if(progress===1){entrance=false;entrancePose=null;pair='intro';syncTimeline(timeline.state());}}
        else {
          const music=window.CourseOpeningAudio?.scoreStatus();
          if(storyScored&&galoisState&&timeline.state().direction>0&&music?.active&&music.scorePlaying&&music.ready&&!music.seeking&&!music.needsSync&&Math.abs(music.currentTime*1000-timeline.state().holdElapsed)<600){
            const position=starts[order.indexOf(9)]+Math.min(story.score.duration,music.currentTime*1000);
            syncTimeline(timeline.seek(routeCycle*timeline.duration+position));
          }else syncTimeline(timeline.advance(dt));
        }
      }
      const captionTarget=caption.classList.contains('is-visible')?1:0;captionOpacity+=(captionTarget-captionOpacity)*(1-Math.exp(-dt/(textFadeMs()/3)));
      if(!outro){
        narration.setScene(narrationIndex(),timeline.state().cycles);
        window.CourseOpeningVoice?.scene(scene,captionTarget===1&&!entrance,timeline.state().direction,timeline.state().cycles,narration.language==='en');
        narration.tick(dt,captionTarget===1&&!entrance,{fadeMs:reduce?0:textFadeMs(),englishMs:scene===9&&storyScored&&galoisState?(galoisNode===6&&timeline.state().holdElapsed>=166000?3500:Math.min(8000,Math.max(1800,(galoisState.holdDuration-2*textFadeMs())/2))):8000,holdEnglish:Boolean(window.CourseOpeningVoice?.holdsScene())});
      }
      const scoredHere=!outro&&!entrance&&storyScored&&Boolean(galoisState);
      window.CourseOpeningAudio?.frame({active:scoredHere,t:scoredHere?timeline.state().holdElapsed/1000:0,dt,direction:timeline.state().direction});
      if(scoredHere&&galoisNode===6){
        const t=timeline.state().holdElapsed,year=t<166000?Math.min(1842,Math.floor(1832+11*Math.max(0,t-143000)/23000)):t<169000?1843:1846;
        root.querySelector('[data-caption-year]').textContent=String(year);root.dataset.galoisRecognition=t>=169000?'published':t>=166000?'recognized':'time';
      }else delete root.dataset.galoisRecognition;
      draw();queue();if(!raf)previous=0;
    }
    function entrancePositions(rect=canvas.getBoundingClientRect()){
      entranceViewport=[rect.width,rect.height];
      return window.CourseOpeningMotion.entrancePositions(grains,Math.max(1,rect.width),Math.max(1,rect.height));
    }
    const diskNormals=new Float32Array(N*3);for(let i=0;i<N;i++)diskNormals[i*3+2]=1;
    function play(){
      stop();impulses.clear();cancelClick();narration.reset();outro=null;galoisState=null;galoisNode=0;displayedGaloisNode=-1;delete root.dataset.outro;panel.querySelector('[data-enter-course]').disabled=false;rebuildDurations();syncCycle(timeline.seek(0));const first=order[0];entrancePortraitWeight=first===9?1:0;entranceGroupWeight=[6,7].includes(first)?1:0;spinAngle=0;routeOffset=0;cameraBridge=null;entrancePose=null;entranceDuration=Math.min(4200,transitions[0]);timeline.seek(0);timeline.setDirection(1);destination=targets[first];source=reduce?targets[first]:entrancePositions();normalSource=reduce?normals[first]:diskNormals;normalDestination=normals[first];extrusionFrom=reduce&&first<5?1:0;extrusionTo=first<5?1:0;twoSidedFrom=reduce&&first===7?1:0;twoSidedTo=first===7?1:0;orbit.pitch=orbit.yaw=orbit.targetPitch=orbit.targetYaw=0;pair=reduce?first+':'+first:'intro';scene=first;progress=reduce?1:0;moving=!reduce;entrance=!reduce;elapsed=0;time=0;sequence=!reduce;active=true;captionOpacity=reduce?1:0;
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
    film={play,stop,refresh,direction,outro:beginOutro,depart,outroReady:()=>outro?.phase==='hold',resetPolyhedra(){geometry.resetPolyhedra();upload();},dispose(){stop();root.removeEventListener('pointerdown',startClick);root.removeEventListener('pointermove',moveClick);root.removeEventListener('pointerup',releaseClick);root.removeEventListener('pointercancel',cancelClick);root.removeEventListener('lostpointercapture',cancelClick);lettering.dispose();if(observer)observer.disconnect();document.removeEventListener('visibilitychange',onVisibility);root.removeEventListener('pointerdown',beginOrbit);root.removeEventListener('pointermove',moveOrbit);for(const name of ['pointerup','pointercancel','lostpointercapture'])root.removeEventListener(name,endOrbit);}};
    root._openingPreview={
      show(index){const slot=order.indexOf(index);if(slot<0)throw new RangeError('Figure is not selected');stop();entrance=false;sequence=false;active=true;pair='preview';syncTimeline(timeline.seek(routeCycle*timeline.duration+starts[slot]+holds[slot]/2));draw();queue();},
      storyNode(index){const slot=order.indexOf(9);if(slot<0)throw new RangeError('Galois is not selected');stop();entrance=false;sequence=false;active=true;syncTimeline(timeline.seek(routeCycle*timeline.duration+starts[slot]+story.atNode(index,storyHoldMs,storyMorphMs,storyScored)));draw();queue();},
      transition(index,value){twoSidedFrom=twoSidedWeight();twoSidedTo=index===7?1:0;manualPortraitWeight=portraitWeight();manualGroupWeight=groupWeight();stop();normalSource=snapshotNormals();source=snapshot(false,time,false);extrusionFrom=0;extrusionTo=index<5?1:0;destination=targets[index];normalDestination=normals[index];scene=index;pair='manual';progress=value;moving=true;entrance=false;sequence=false;active=true;upload();updateCaption();showCaption(false);draw();queue();},
      settings(value){Object.assign(settings,value);updateSettings();},
      atTime(value){time=value;Object.assign(visual,{camera:effective().camera,background:effective().background,spotlight:effective().spotlight,radiation:effective().radiation,spin:effective().spin});spinAngle=Math.atan2(Math.sin(value*visual.spin*spinDirection()),Math.cos(value*visual.spin*spinDirection()));draw();},
      seek(value){entrance=false;sequence=false;active=true;syncTimeline(timeline.seek(value));draw();},
      advance(value){entrance=false;syncTimeline(timeline.advance(value));draw();},
      direction(value,engage=false){syncTimeline(timeline.setDirection(value,engage));draw();},
      evidence(){return{storyTreatment:storyTreatment(),galoisStory:{node:galoisNode,state:galoisState,hold:storyHoldMs,morph:storyMorphMs,nodes:story.nodes.length,scored:storyScored,music:window.CourseOpeningAudio?.scoreStatus()},outro:outro?{phase:outro.phase,elapsed:outro.elapsed,view:outro.view}:null,count:N,stride:3,scene,progress,time,entrance,entranceElapsed:elapsed,entranceDuration,positions:snapshot(),visiblePositions:snapshot(true),targets,settings:{...settings},effective:effective(),rendered:{...visual},camera:cameraPose(),orbit:{...orbit},spinAngle:renderedSpin(),spinPhase:spinAngle,portraitWeight:portraitWeight(),groupWeight:groupWeight(),twoSidedWeight:twoSidedWeight(),impulses:impulses.evidence(),spinVelocity:visual.spin*spinDirection()*(1-portraitWeight()),motion:motion.evidence(),routeOffset,cameraBridge:cameraBridge?{elapsed:cameraBridge.elapsed,duration:cameraBridge.duration}:null,order:[...order],nextOrder:playlist.order(routeCycle+1),routeCycle,holds:[...holds],transitions:[...transitions],cameraRig:cameraRig.evidence(),timeline:timeline.state(),duration:timeline.duration,starts,geometry:geometry.evidence(),glError:gl.getError()};}
    };
    document.addEventListener('visibilitychange',onVisibility);observer=new ResizeObserver(draw);observer.observe(canvas);
    boot.advance(95,'准备呈现');updateCaption();draw();await paint();root.dataset.particleCount=String(N);root.dataset.ready='true';boot.advance(100,'准备完成');await paint();
  }
  if(!location.hash&&!window.courseOpeningDismissed)openOpening();
  else document.documentElement.classList.remove('course-opening-pending');
})();
