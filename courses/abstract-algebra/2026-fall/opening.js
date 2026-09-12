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
  const storageKey = 'courseOpeningAppearance.v1';
  const defaults = Object.freeze({colorEnabled:false,colorAmount:.4,complexityEnabled:false,complexityAmount:.5,depthEnabled:true,wanderEnabled:!reduce,wanderAmount:.22});
  let settings = {...defaults};
  try {
    const saved = JSON.parse(localStorage.getItem(storageKey) || '{}');
    for (const key of Object.keys(defaults)) {
      if (typeof defaults[key] === 'boolean' && typeof saved[key] === 'boolean') settings[key] = saved[key];
      else if (typeof defaults[key] === 'number' && Number.isFinite(saved[key])) settings[key] = Math.max(0,Math.min(1,saved[key]));
    }
  } catch (_) {}
  if (reduce) settings.wanderEnabled = false;
  let film = null, initialization = null, visibilityTimer = 0;
  function effective() {return {colorAmount:settings.colorEnabled?settings.colorAmount:0,complexity:settings.complexityEnabled?settings.complexityAmount:0,depth:settings.depthEnabled?1:0,wander:settings.wanderEnabled?settings.wanderAmount:0};}
  function syncSettings() {
    root.dataset.settings = JSON.stringify(settings);
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
    else return;
    updateSettings();
  });
  panel.querySelector('[data-settings-reset]').addEventListener('click',()=>{settings={...defaults};updateSettings();});
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
    if(film)film.stop();boot.stop();panel.hidden=true;dialog.classList.remove('settings-open','has-pointer-controls');toggle.setAttribute('aria-expanded','false');clearTimeout(visibilityTimer);
    if(dialog.open)dialog.close();document.body.classList.remove('opening-active');document.documentElement.classList.remove('course-opening-pending');
    const main=document.getElementById('main');if(main){main.setAttribute('tabindex','-1');main.focus({preventScroll:true});}
  }
  async function openOpening() {
    if(root.dataset.contextLost==='true')return;
    const alreadyLoading=dialog.open&&dialog.classList.contains('opening-loading');
    if(dialog.open&&!alreadyLoading)return;
    if(!dialog.open) { if(film){dialog.showModal();dialog.focus({preventScroll:true});document.body.classList.add('opening-active');}else boot.start(); }
    try {
      if(!initialization)initialization=initialize();await initialization;
      if(dialog.open){boot.finish();dialog.classList.remove('opening-loading');dialog.classList.add('opening-ready');film.play();}
    }catch(error){root.dataset.unavailable='true';leaveOpening();initialization=null;}
  }
  dialog.addEventListener('keydown',event=>{
    if(event.key===' '&&!event.repeat&&!panel.contains(event.target)&&event.target!==toggle){event.preventDefault();leaveOpening();}
  });
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
    const geometry=window.CourseOpeningGeometry, materials=window.CourseOpeningMaterials;
    const gl=canvas.getContext('webgl',{alpha:false,antialias:false,preserveDrawingBuffer:true});
    if(!gl||!geometry||!materials)throw new Error('Opening unavailable');
    const N=geometry.count,targets=[];
    boot.advance(22,'生成对称图形');await paint();
    for(let i=0;i<geometry.captions.length;i++){
      targets.push(geometry.create(i));root.dataset.prepared=String(i+1);boot.advance(22+(i+1)*11,i===4?'生成 Julia 分形':'生成对称图形');await paint();
    }
    boot.advance(82,'雕琢沙粒质感');await paint();
    const bgv = 'attribute vec2 pos;varying vec2 uv;void main(){uv=pos;gl_Position=vec4(pos,0.,1.);}';
    const bgf = `precision highp float;varying vec2 uv;
      float hash(vec2 p){return fract(sin(dot(p,vec2(127.1,311.7)))*43758.5453);}
      void main(){float noise=hash(floor(gl_FragCoord.xy))*.009;
        float lamp=exp(-length((uv-vec2(-.5,.45))*vec2(.7,1.)))*.015;
        float v=1.-smoothstep(.25,1.5,length(uv));
        gl_FragColor=vec4(vec3(.018,.017,.014)+vec3(.6,.49,.28)*(lamp+noise)*v,1.);}`;
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
    const program = link(materials.vertex, materials.fragment), background = link(bgv, bgf);
    const quad = buffer(new Float32Array([-1,-1,1,-1,-1,1,-1,1,1,-1,1,1]), gl.STATIC_DRAW);
    let source=targets[0].slice(), destination=targets[0];
    const sourceBuffer=buffer(source,gl.DYNAMIC_DRAW),destinationBuffer=buffer(destination,gl.DYNAMIC_DRAW);
    let seed=317129;const grains=new Float32Array(N*4);
    for(let i=0;i<grains.length;i++){seed=(Math.imul(seed,1664525)+1013904223)>>>0;grains[i]=seed/4294967296;}
    const grainBuffer=buffer(grains,gl.STATIC_DRAW);
    const loc={source:gl.getAttribLocation(program,'start'),destination:gl.getAttribLocation(program,'finish'),grain:gl.getAttribLocation(program,'grain'),quad:gl.getAttribLocation(background,'pos')};
    for(const name of ['progress','aspect','dpr','time','colorAmount','complexity','depth','wander'])loc[name]=gl.getUniformLocation(program,name);
    function attribute(data,location,size){gl.bindBuffer(gl.ARRAY_BUFFER,data);gl.enableVertexAttribArray(location);gl.vertexAttribPointer(location,size,gl.FLOAT,false,0,0);}
    let scene=0,progress=1,moving=false,active=false,sequence=false,entrance=false,elapsed=0,time=0,previous=0,raf=0;
    const holds=[4600,4600,4600,7200,8400];
    const ease=t=>t*t*t*(t*(t*6-15)+10);
    function snapshot(withWander=false,atTime=time){
      const e=ease(progress),arch=Math.sin(Math.PI*e),result=new Float32Array(N*2),amount=effective().wander;
      for(let i=0;i<N;i++){
        const k=i*2,dx=destination[k]-source[k],dy=destination[k+1]-source[k+1],drift=arch*Math.min(.022,Math.hypot(dx,dy)*.16);
        let x=source[k]+dx*e-dy*arch*.28+Math.sin(grains[i*4]*19+e*6.283)*drift;
        let y=source[k+1]+dy*e+dx*arch*.28+Math.cos(grains[i*4+1]*23-e*6.283)*drift;
        if(withWander){const d=materials.localOffset(x,y,grains[i*4],grains[i*4+1],grains[i*4+2],grains[i*4+3],atTime,amount);x+=d[0];y+=d[1];}
        result[k]=x;result[k+1]=y;
      }return result;
    }
    function upload(){gl.bindBuffer(gl.ARRAY_BUFFER,sourceBuffer);gl.bufferSubData(gl.ARRAY_BUFFER,0,source);gl.bindBuffer(gl.ARRAY_BUFFER,destinationBuffer);gl.bufferSubData(gl.ARRAY_BUFFER,0,destination);}
    function updateCaption(){const text=geometry.captions[scene];root.querySelector('[data-caption-title]').textContent=text.title;root.querySelector('[data-caption-zh]').textContent=text.zh;root.querySelector('[data-caption-en]').textContent=text.en;canvas.setAttribute('aria-label',text.title+'。'+text.zh);}
    function draw(){
      if(!dialog.open)return;
      const rect=canvas.getBoundingClientRect(),ratio=Math.min(2,window.devicePixelRatio||1),width=Math.max(1,Math.round(rect.width*ratio)),height=Math.max(1,Math.round(rect.height*ratio));
      if(canvas.width!==width||canvas.height!==height){canvas.width=width;canvas.height=height;}
      gl.viewport(0,0,width,height);gl.disable(gl.BLEND);gl.useProgram(background);attribute(quad,loc.quad,2);gl.drawArrays(gl.TRIANGLES,0,6);
      gl.useProgram(program);attribute(sourceBuffer,loc.source,2);attribute(destinationBuffer,loc.destination,2);attribute(grainBuffer,loc.grain,4);gl.enable(gl.BLEND);gl.blendFunc(gl.SRC_ALPHA,gl.ONE_MINUS_SRC_ALPHA);
      gl.uniform1f(loc.progress,progress);gl.uniform1f(loc.aspect,width/height);gl.uniform1f(loc.dpr,ratio*Math.max(1,Math.min(1.4,rect.height/800)));gl.uniform1f(loc.time,time);
      for(const [name,value] of Object.entries(effective()))gl.uniform1f(loc[name],value);
      gl.drawArrays(gl.POINTS,0,N);root.dataset.scene=String(scene);root.dataset.progress=progress.toFixed(4);root.dataset.time=time.toFixed(3);
    }
    function moveTo(index){source=snapshot();destination=targets[index];scene=index;progress=0;moving=true;entrance=false;elapsed=0;caption.classList.remove('is-visible');upload();updateCaption();draw();}
    function stop(){active=false;previous=0;cancelAnimationFrame(raf);raf=0;}
    function queue(){if(!raf&&active&&dialog.open&&!document.hidden&&(sequence||effective().wander>0))raf=requestAnimationFrame(tick);}
    function tick(now){
      raf=0;if(!active||!dialog.open||document.hidden)return;
      const dt=previous?Math.min(100,now-previous):0;previous=now;time+=dt/1000;
      if(sequence&&panel.hidden){
        elapsed+=dt;
        if(moving){progress=Math.min(1,elapsed/(entrance?2300:scene===4?5200:4200));if(progress===1){moving=false;entrance=false;elapsed=0;}}
        else{
          if(elapsed>420)caption.classList.add('is-visible');
          if(elapsed>holds[scene]-600&&scene<targets.length-1)caption.classList.remove('is-visible');
          if(elapsed>=holds[scene]){if(scene+1<targets.length)moveTo(scene+1);else sequence=false;}
        }
      }
      if(moving||effective().wander>0||sequence)draw();
      queue();if(!raf)previous=0;
    }
    function entrancePositions(){
      const rect=canvas.getBoundingClientRect(),aspect=rect.width/rect.height,fit=Math.min(.68,aspect*.84);
      const t=Math.max(0,Math.min(1,(aspect-.8)/.5)),offset=.05+.15*t*t*(3-2*t);
      const half=Math.min(320,rect.width*.7)*.88/(rect.height*fit),line=new Float32Array(N*2);
      for(let i=0;i<N;i++){line[i*2]=(grains[i*4]*2-1)*half;line[i*2+1]=-offset/fit+(grains[i*4+1]-.5)*.009;}
      return line;
    }
    function play(){
      stop();destination=targets[0];source=reduce?targets[0].slice():entrancePositions();scene=0;progress=reduce?1:0;moving=!reduce;entrance=!reduce;elapsed=0;time=0;sequence=!reduce;active=true;upload();updateCaption();draw();caption.classList.toggle('is-visible',reduce);queue();
    }
    function refresh(){draw();queue();}
    let observer;
    function onVisibility(){previous=0;if(document.hidden){cancelAnimationFrame(raf);raf=0;}else queue();}
    film={play,stop,refresh,dispose(){stop();if(observer)observer.disconnect();document.removeEventListener('visibilitychange',onVisibility);}};
    root._openingPreview={
      show(index){stop();scene=index;source=targets[index].slice();destination=targets[index];progress=1;moving=false;sequence=false;active=true;upload();updateCaption();draw();caption.classList.add('is-visible');queue();},
      transition(index,value){stop();moveTo(index);progress=value;sequence=false;active=true;draw();queue();},
      settings(value){Object.assign(settings,value);updateSettings();},
      atTime(value){time=value;draw();},
      evidence(){return{count:N,scene,progress,time,positions:snapshot(),visiblePositions:snapshot(true),targets,settings:{...settings},effective:effective(),geometry:geometry.evidence(),glError:gl.getError()};}
    };
    document.addEventListener('visibilitychange',onVisibility);observer=new ResizeObserver(draw);observer.observe(canvas);
    boot.advance(95,'准备呈现');updateCaption();draw();await paint();
    root.dataset.particleCount=String(N);root.dataset.ready='true';boot.advance(100,'准备完成');await paint();
  }
  if(!location.hash&&!window.courseOpeningDismissed)openOpening();
  else document.documentElement.classList.remove('course-opening-pending');
})();
