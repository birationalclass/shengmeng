(() => {
  'use strict';
  const dialog = document.getElementById('courseOpening');
  const root = document.getElementById('symmetry-particle-studies');
  const canvas = root.querySelector('.opening-grains');
  const caption = root.querySelector('.opening-caption');
  const panel = document.getElementById('openingSettings');
  const toggle = document.getElementById('openingSettingsToggle');
  const boot = window.CourseOpeningBoot;
  const reduce = matchMedia('(prefers-reduced-motion: reduce)').matches;
  // A new preference edition enables the newly added effects once for returning visitors.
  const storageKey = 'courseOpeningAppearance.v2';
  const durationChoices = [5,10,15,20,30];
  const defaults = Object.freeze({colorEnabled:true,colorAmount:.4,complexityEnabled:true,complexityAmount:.5,depthEnabled:true,wanderEnabled:true,wanderAmount:.22,cameraEnabled:true,backgroundEnabled:true,radiationEnabled:true,radiationAmount:.45,sceneDurations:Object.freeze([10,10,10,10,10,10])});
  const freshDefaults=()=>({...defaults,sceneDurations:[...defaults.sceneDurations]});
  let settings = freshDefaults();
  try {
    const saved = JSON.parse(localStorage.getItem(storageKey) || '{}');
    for (const key of Object.keys(defaults)) {
      if (typeof defaults[key] === 'boolean' && typeof saved[key] === 'boolean') settings[key] = saved[key];
      else if (typeof defaults[key] === 'number' && Number.isFinite(saved[key])) settings[key] = Math.max(0,Math.min(1,saved[key]));
    }
    if(Array.isArray(saved.sceneDurations))settings.sceneDurations=defaults.sceneDurations.map((value,i)=>durationChoices.includes(saved.sceneDurations[i])?saved.sceneDurations[i]:value);
  } catch (_) {}
  let film = null, initialization = null, visibilityTimer = 0, stage = 'loading', ownedFullscreen = false, entryVersion = 0;
  toggle.disabled=true;
  const startButton=root.querySelector('[data-start-animation]');
  function effective() {return {colorAmount:settings.colorEnabled?settings.colorAmount:0,complexity:settings.complexityEnabled?settings.complexityAmount:0,depth:settings.depthEnabled?1:0,wander:settings.wanderEnabled?settings.wanderAmount:0,camera:settings.cameraEnabled?1:0,background:settings.backgroundEnabled?1:0,radiation:settings.radiationEnabled?settings.radiationAmount:0};}
  function syncSettings() {
    root.dataset.settings = JSON.stringify(settings);
    root.classList.toggle('can-orbit',settings.depthEnabled);
    panel.querySelectorAll('[data-scene-duration]').forEach(input=>input.value=String(settings.sceneDurations[Number(input.dataset.sceneDuration)]));
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
    if(input.dataset.settingToggle)settings[input.dataset.settingToggle]=input.checked;
    else if(input.dataset.settingRange)settings[input.dataset.settingRange]=Number(input.value)/100;
    else if(input.dataset.sceneDuration!==undefined&&durationChoices.includes(Number(input.value)))settings.sceneDurations[Number(input.dataset.sceneDuration)]=Number(input.value);
    else return;
    updateSettings();
  });
  panel.querySelector('[data-settings-reset]').addEventListener('click',()=>{settings=freshDefaults();updateSettings();});
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
  function leaveOpening() {
    entryVersion++;stage='closed';root.dataset.stage=stage;toggle.disabled=true;
    if(ownedFullscreen&&document.fullscreenElement){ownedFullscreen=false;document.exitFullscreen().catch(()=>{});}
    window.CourseOpeningAudio?.stop();
    if(film)film.stop();boot.stop();panel.hidden=true;dialog.classList.remove('settings-open','has-pointer-controls');toggle.setAttribute('aria-expanded','false');clearTimeout(visibilityTimer);
    if(dialog.open)dialog.close();document.body.classList.remove('opening-active');document.documentElement.classList.remove('course-opening-pending');
    const main=document.getElementById('main');if(main){main.setAttribute('tabindex','-1');main.focus({preventScroll:true});}
  }
  async function openOpening() {
    if(root.dataset.contextLost==='true')return;
    const alreadyLoading=dialog.open&&dialog.classList.contains('opening-loading');
    if(dialog.open&&!alreadyLoading)return;
    if(!dialog.open)boot.start();
    const entry=++entryVersion;stage='loading';root.dataset.stage=stage;toggle.disabled=true;
    try {
      if(!initialization)initialization=initialize();await initialization;
      if(entry===entryVersion&&dialog.open){stage='ready';root.dataset.stage=stage;boot.ready();dialog.classList.remove('opening-loading');dialog.classList.add('opening-awaiting-start');}
    }catch(error){if(entry===entryVersion){root.dataset.unavailable='true';leaveOpening();initialization=null;}}
  }
  async function startAnimation() {
    if(stage!=='ready'||!film)return;
    const entry=++entryVersion;let enteredFullscreen=false;
    stage='starting';root.dataset.stage=stage;startButton.disabled=true;
    window.CourseOpeningAudio?.start();
    try {
      if(!document.fullscreenElement){
        if(!root.requestFullscreen)throw new Error('Fullscreen unavailable');
        await root.requestFullscreen({navigationUI:'hide'});enteredFullscreen=true;
      }
      if(entry!==entryVersion||stage!=='starting'||!dialog.open){if(enteredFullscreen&&document.fullscreenElement===root&&stage!=='playing')document.exitFullscreen().catch(()=>{});return;}
      ownedFullscreen=enteredFullscreen||ownedFullscreen;
      stage='playing';root.dataset.stage=stage;delete root.dataset.fullscreenBlocked;
      dialog.classList.remove('opening-loading','opening-awaiting-start');dialog.classList.add('opening-ready');
      boot.finish();toggle.disabled=false;dialog.focus({preventScroll:true});film.play();
    }catch(error){
      if(entry!==entryVersion)return;
      window.CourseOpeningAudio?.stop();
      stage='ready';root.dataset.stage=stage;root.dataset.fullscreenBlocked='true';startButton.disabled=false;
      startButton.textContent='点击重试全屏';root.querySelector('[data-loading-status]').textContent='请允许浏览器全屏后开始';
    }
  }
  dialog.addEventListener('click',()=>{if(stage==='ready')startAnimation();});
  dialog.addEventListener('keydown',event=>{
    if(event.key===' '&&!event.repeat&&!panel.contains(event.target)){
      event.preventDefault();if(stage==='ready')startAnimation();else if(stage==='playing')leaveOpening();
    }
  });
  dialog.addEventListener('wheel',event=>{
    if(stage!=='playing'||panel.contains(event.target)||event.ctrlKey||Math.abs(event.deltaY)<.5)return;
    event.preventDefault();film.direction(event.deltaY>0?1:-1);showControls();
  },{passive:false});
  document.addEventListener('fullscreenchange',()=>{if(stage==='playing'&&!document.fullscreenElement)leaveOpening();});
  dialog.addEventListener('cancel',event=>{event.preventDefault();if(!panel.hidden)closeSettings(true);else leaveOpening();});
  panel.querySelector('[data-enter-course]').addEventListener('click',leaveOpening);
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
    const N=geometry.count,targets=[],normals=[];
    boot.advance(22,'生成对称图形');await paint();
    for(let i=0;i<geometry.captions.length;i++){
      targets.push(geometry.create3D(i));normals.push(geometry.createNormals(i));root.dataset.prepared=String(i+1);boot.advance(22+(i+1)/geometry.captions.length*55,i===5?'铸造万环之环':i===4?'生成 Julia 分形':'生成对称图形');await paint();
    }
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
    const quad = buffer(new Float32Array([-1,-1,1,-1,-1,1,-1,1,1,-1,1,1]), gl.STATIC_DRAW);
    let source=targets[0],destination=targets[0],normalSource=normals[0],normalDestination=normals[0],extrusionFrom=1,extrusionTo=1;
    const sourceBuffer=buffer(source,gl.DYNAMIC_DRAW),destinationBuffer=buffer(destination,gl.DYNAMIC_DRAW);
    const normalSourceBuffer=buffer(normalSource,gl.DYNAMIC_DRAW),normalDestinationBuffer=buffer(normalDestination,gl.DYNAMIC_DRAW);
    let seed=317129;const grains=new Float32Array(N*4);
    for(let i=0;i<grains.length;i++){seed=(Math.imul(seed,1664525)+1013904223)>>>0;grains[i]=seed/4294967296;}
    const grainBuffer=buffer(grains,gl.STATIC_DRAW);
    const loc={source:gl.getAttribLocation(program,'start'),destination:gl.getAttribLocation(program,'finish'),normalSource:gl.getAttribLocation(program,'normalStart'),normalDestination:gl.getAttribLocation(program,'normalFinish'),grain:gl.getAttribLocation(program,'grain'),quad:gl.getAttribLocation(background,'pos')};
    for(const name of ['progress','aspect','dpr','time','colorAmount','complexity','depth','wander','camera','radiation','viewAngles','viewZoom','extrusionFrom','extrusionTo'])loc[name]=gl.getUniformLocation(program,name);
    const bgLoc={};for(const name of ['time','aspect','camera','background','viewAngles','viewZoom'])bgLoc[name]=gl.getUniformLocation(background,name);
    function attribute(data,location,size){gl.bindBuffer(gl.ARRAY_BUFFER,data);gl.enableVertexAttribArray(location);gl.vertexAttribPointer(location,size,gl.FLOAT,false,0,0);}
    const transitions=[4200,4200,4200,5200,5400,5000];
    let holds=settings.sceneDurations.map(value=>value*1000);
    let timeline=window.CourseOpeningTimeline.create({holds,transitions});
    const makeStarts=()=>holds.map((_,i)=>holds.slice(0,i).reduce((sum,x,j)=>sum+x+transitions[j],0));
    let starts=makeStarts();
    let scene=0,progress=1,moving=false,active=false,sequence=false,entrance=false,elapsed=0,time=0,previous=0,raf=0,pair='0:0';
    const visual={camera:0,background:0,radiation:0};
    const orbit={pitch:0,yaw:0,targetPitch:0,targetYaw:0,pointer:null,x:0,y:0};
    const ease=t=>t*t*t*(t*(t*6-15)+10);
    function snapshot(withEffects=false,atTime=time){
      const e=ease(progress),arch=Math.sin(Math.PI*e),result=new Float32Array(N*3),appearance=effective();
      for(let i=0;i<N;i++){
        const k=i*3,g=i*4,dx=destination[k]-source[k],dy=destination[k+1]-source[k+1],drift=arch*Math.min(.022,Math.hypot(dx,dy)*.16);
        let x=source[k]+dx*e-dy*arch*.28+Math.sin(grains[g]*19+e*6.283)*drift;
        let y=source[k+1]+dy*e+dx*arch*.28+Math.cos(grains[g+1]*23-e*6.283)*drift;
        const fromZ=source[k+2]*(1-extrusionFrom+extrusionFrom*appearance.depth),toZ=destination[k+2]*(1-extrusionTo+extrusionTo*appearance.depth);
        let z=fromZ+(toZ-fromZ)*e;
        if(withEffects){
          const d=materials.localOffset(x,y,grains[g],grains[g+1],grains[g+2],grains[g+3],atTime,appearance.wander);x+=d[0];y+=d[1];
          const escaped=materials.radiationOffset(x,y,z,grains[g],grains[g+1],grains[g+2],grains[g+3],atTime,visual.radiation);x+=escaped.offset[0];y+=escaped.offset[1];z+=escaped.offset[2];
        }
        result[k]=x;result[k+1]=y;result[k+2]=z;
      }return result;
    }
    function snapshotNormals(){const e=ease(progress),out=new Float32Array(N*3),flat=1-effective().depth;for(let i=0;i<out.length;i++){const face=i%3===2?1:0,a=normalSource[i]+(face-normalSource[i])*extrusionFrom*flat,b=normalDestination[i]+(face-normalDestination[i])*extrusionTo*flat;out[i]=a+(b-a)*e;}return out;}
    function upload(){for(const [buf,data] of [[sourceBuffer,source],[destinationBuffer,destination],[normalSourceBuffer,normalSource],[normalDestinationBuffer,normalDestination]]){gl.bindBuffer(gl.ARRAY_BUFFER,buf);gl.bufferSubData(gl.ARRAY_BUFFER,0,data);}}
    function updateCaption(){const text=geometry.captions[scene];root.querySelector('[data-caption-title]').textContent=text.title;root.querySelector('[data-caption-zh]').textContent=text.zh;root.querySelector('[data-caption-en]').textContent=text.en;canvas.setAttribute('aria-label',text.title+'。'+text.zh);}
    function syncTimeline(state){
      const key=state.from+':'+state.to;
      if(key!==pair){pair=key;source=targets[state.from];destination=targets[state.to];normalSource=normals[state.from];normalDestination=normals[state.to];extrusionFrom=state.from<5?1:0;extrusionTo=state.to<5?1:0;upload();}
      progress=state.progress;moving=state.moving;
      const label=state.moving?(state.direction>0?state.to:state.from):state.scene;
      if(scene!==label){scene=label;updateCaption();}
      const spent=state.direction>0?state.holdElapsed:state.holdDuration-state.holdElapsed;
      const remaining=state.direction>0?state.holdDuration-state.holdElapsed:state.holdElapsed;
      caption.classList.toggle('is-visible',!state.moving&&spent>420&&remaining>600);
    }
    function cameraPose(){
      const state=timeline.state();
      let pose;
      if(entrance)pose=cameraRig.blend({angles:[0,0,0],zoom:1},cameraRig.sample(0,0),ease(progress));
      else if(state.moving)pose=cameraRig.blend(cameraRig.sample(state.from,1),cameraRig.sample(state.to,0),ease(state.progress));
      else pose=cameraRig.sample(state.scene,state.holdElapsed/state.holdDuration);
      return {angles:[pose.angles[0]*visual.camera+orbit.pitch,pose.angles[1]*visual.camera+orbit.yaw,pose.angles[2]*visual.camera],zoom:1+(pose.zoom-1)*visual.camera,perspective:Math.max(visual.camera,settings.depthEnabled?1:0)};
    }
    function rebuildDurations(){
      const next=settings.sceneDurations.map(value=>value*1000);
      if(next.every((value,i)=>value===holds[i]))return;
      const old=timeline.state();holds=next;starts=makeStarts();timeline=window.CourseOpeningTimeline.create({holds,transitions});
      const position=old.moving?starts[old.from]+holds[old.from]+old.progress*transitions[old.from]:starts[old.scene]+old.holdElapsed/old.holdDuration*holds[old.scene];
      timeline.seek(position+old.cycles*timeline.duration);timeline.setDirection(old.direction);
      if(!entrance)syncTimeline(timeline.state());
    }
    function endOrbit(event){
      if(orbit.pointer===null||event&&event.pointerId!==orbit.pointer)return;
      if(root.hasPointerCapture(orbit.pointer))root.releasePointerCapture(orbit.pointer);
      orbit.pointer=null;root.classList.remove('is-orbiting');previous=0;queue();
    }
    function beginOrbit(event){
      if(stage!=='playing'||!settings.depthEnabled||event.button!==0||!event.isPrimary||panel.contains(event.target)||event.target.closest('button,a,input,select,summary'))return;
      orbit.pointer=event.pointerId;orbit.x=event.clientX;orbit.y=event.clientY;
      root.setPointerCapture(event.pointerId);root.classList.add('is-orbiting');event.preventDefault();queue();
    }
    function moveOrbit(event){
      if(event.pointerId!==orbit.pointer)return;
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
      if(canvas.width!==width||canvas.height!==height){canvas.width=width;canvas.height=height;}
      const view=cameraPose();
      gl.viewport(0,0,width,height);gl.disable(gl.DEPTH_TEST);gl.depthMask(false);gl.disable(gl.BLEND);gl.useProgram(background);
      gl.uniform1f(bgLoc.time,time);gl.uniform1f(bgLoc.aspect,width/height);gl.uniform1f(bgLoc.camera,view.perspective);gl.uniform3fv(bgLoc.viewAngles,view.angles);gl.uniform1f(bgLoc.viewZoom,view.zoom);gl.uniform1f(bgLoc.background,visual.background);
      attribute(quad,loc.quad,2);gl.drawArrays(gl.TRIANGLES,0,6);
      gl.depthMask(true);gl.clearDepth(1);gl.clear(gl.DEPTH_BUFFER_BIT);gl.enable(gl.DEPTH_TEST);gl.depthFunc(gl.LEQUAL);
      gl.useProgram(program);attribute(sourceBuffer,loc.source,3);attribute(destinationBuffer,loc.destination,3);attribute(normalSourceBuffer,loc.normalSource,3);attribute(normalDestinationBuffer,loc.normalDestination,3);attribute(grainBuffer,loc.grain,4);
      gl.enable(gl.BLEND);gl.blendFunc(gl.SRC_ALPHA,gl.ONE_MINUS_SRC_ALPHA);
      gl.uniform1f(loc.progress,progress);gl.uniform1f(loc.aspect,width/height);gl.uniform1f(loc.dpr,ratio*Math.max(1,Math.min(1.4,rect.height/800)));gl.uniform1f(loc.time,time);
      const appearance=effective();for(const name of ['colorAmount','complexity','depth','wander'])gl.uniform1f(loc[name],appearance[name]);gl.uniform1f(loc.camera,view.perspective);gl.uniform3fv(loc.viewAngles,view.angles);gl.uniform1f(loc.viewZoom,view.zoom);gl.uniform1f(loc.extrusionFrom,extrusionFrom);gl.uniform1f(loc.extrusionTo,extrusionTo);gl.uniform1f(loc.radiation,visual.radiation);
      gl.drawArrays(gl.POINTS,0,N);root.dataset.scene=String(scene);root.dataset.progress=progress.toFixed(4);root.dataset.time=time.toFixed(3);root.dataset.direction=String(timeline.state().direction);root.dataset.cycles=String(timeline.state().cycles);
    }
    function stop(){endOrbit();active=false;previous=0;cancelAnimationFrame(raf);raf=0;}
    function needsFrames(){const target=effective();return orbit.pointer!==null||Math.abs(orbit.pitch-orbit.targetPitch)+Math.abs(orbit.yaw-orbit.targetYaw)>.0001||sequence||target.wander>0||visual.camera>0||visual.radiation>0||Object.keys(visual).some(key=>Math.abs(visual[key]-target[key])>.0001);}
    function queue(){if(!raf&&active&&dialog.open&&!document.hidden&&needsFrames())raf=requestAnimationFrame(tick);}
    function tick(now){
      raf=0;if(!active||!dialog.open||document.hidden)return;
      const dt=previous?Math.min(100,now-previous):0;previous=now;time+=dt/1000;
      const target=effective(),blend=1-Math.exp(-dt/460);
      for(const key of Object.keys(visual)){visual[key]+=(target[key]-visual[key])*blend;if(Math.abs(visual[key]-target[key])<.0001)visual[key]=target[key];}
      const damping=1-Math.exp(-cameraRig.manual.responsePerSecond*dt/1000);
      orbit.pitch+=(orbit.targetPitch-orbit.pitch)*damping;orbit.yaw+=(orbit.targetYaw-orbit.yaw)*damping;
      if(sequence&&panel.hidden&&orbit.pointer===null){
        if(entrance){elapsed+=dt;progress=Math.min(1,elapsed/2300);if(progress===1){entrance=false;pair='intro';syncTimeline(timeline.state());}}
        else syncTimeline(timeline.advance(dt));
      }
      draw();queue();if(!raf)previous=0;
    }
    function entrancePositions(){
      const rect=canvas.getBoundingClientRect(),aspect=rect.width/rect.height,fit=Math.min(.68,aspect*.84),t=Math.max(0,Math.min(1,(aspect-.8)/.5)),offset=.05+.15*t*t*(3-2*t);
      const half=Math.min(320,rect.width*.7)*.88/(rect.height*fit),line=new Float32Array(N*3);
      for(let i=0;i<N;i++){line[i*3]=(grains[i*4]*2-1)*half;line[i*3+1]=-offset/fit+(grains[i*4+1]-.5)*.009;}
      return line;
    }
    function play(){
      stop();timeline.seek(0);timeline.setDirection(1);destination=targets[0];source=reduce?targets[0]:entrancePositions();normalSource=normals[0];normalDestination=normals[0];extrusionFrom=reduce?1:0;extrusionTo=1;orbit.pitch=orbit.yaw=orbit.targetPitch=orbit.targetYaw=0;pair=reduce?'0:0':'intro';scene=0;progress=reduce?1:0;moving=!reduce;entrance=!reduce;elapsed=0;time=0;sequence=!reduce;active=true;
      for(const key of Object.keys(visual))visual[key]=0;
      upload();updateCaption();draw();caption.classList.toggle('is-visible',reduce);queue();
    }
    function direction(value){
      if(entrance){timeline.setDirection(value,false);root.dataset.direction=String(value);return;}
      syncTimeline(timeline.setDirection(value,!settings.cameraEnabled));sequence=true;active=true;draw();queue();
    }
    function refresh(){rebuildDurations();if(!settings.depthEnabled){endOrbit();orbit.targetPitch=orbit.targetYaw=0;}draw();queue();}
    let observer;
    function onVisibility(){previous=0;if(document.hidden){cancelAnimationFrame(raf);raf=0;}else queue();}
    film={play,stop,refresh,direction,dispose(){stop();if(observer)observer.disconnect();document.removeEventListener('visibilitychange',onVisibility);root.removeEventListener('pointerdown',beginOrbit);root.removeEventListener('pointermove',moveOrbit);for(const name of ['pointerup','pointercancel','lostpointercapture'])root.removeEventListener(name,endOrbit);}};
    root._openingPreview={
      show(index){stop();entrance=false;sequence=false;active=true;pair='preview';syncTimeline(timeline.seek(starts[index]+holds[index]/2));draw();queue();},
      transition(index,value){stop();normalSource=snapshotNormals();source=snapshot();extrusionFrom=0;extrusionTo=index<5?1:0;destination=targets[index];normalDestination=normals[index];scene=index;pair='manual';progress=value;moving=true;entrance=false;sequence=false;active=true;upload();updateCaption();caption.classList.remove('is-visible');draw();queue();},
      settings(value){Object.assign(settings,value);updateSettings();},
      atTime(value){time=value;Object.assign(visual,{camera:effective().camera,background:effective().background,radiation:effective().radiation});draw();},
      seek(value){entrance=false;sequence=false;active=true;syncTimeline(timeline.seek(value));draw();},
      advance(value){entrance=false;syncTimeline(timeline.advance(value));draw();},
      direction(value,engage=false){syncTimeline(timeline.setDirection(value,engage));draw();},
      evidence(){return{count:N,stride:3,scene,progress,time,positions:snapshot(),visiblePositions:snapshot(true),targets,settings:{...settings},effective:effective(),rendered:{...visual},camera:cameraPose(),orbit:{...orbit},holds:[...holds],timeline:timeline.state(),duration:timeline.duration,starts,geometry:geometry.evidence(),glError:gl.getError()};}
    };
    document.addEventListener('visibilitychange',onVisibility);observer=new ResizeObserver(draw);observer.observe(canvas);
    boot.advance(95,'准备呈现');updateCaption();draw();await paint();root.dataset.particleCount=String(N);root.dataset.ready='true';boot.advance(100,'准备完成');await paint();
  }
  if(!location.hash&&!window.courseOpeningDismissed)openOpening();
  else document.documentElement.classList.remove('course-opening-pending');
})();
