/* Continue the opening's downward sand streams after the title has docked. */
(()=>{
  const title=document.querySelector('.hero h1');if(!title)return;
  const reduced=matchMedia('(prefers-reduced-motion:reduce)');
  const animated=()=>!reduced.matches&&document.documentElement.dataset.sandMotion!=='off';
  const canvas=document.createElement('canvas');canvas.className='course-hero-sand';canvas.setAttribute('aria-hidden','true');
  const ctx=canvas.getContext('2d');if(!ctx)return;
  let points=[],frame=0,last=0,queued=0,inView=true,width=0,height=0,tail=0,bridging=false,geometryKey='',fontReady=false;
  const smooth=(a,b,x)=>{const t=Math.max(0,Math.min(1,(x-a)/(b-a)));return t*t*(3-2*t);};
  // Same 3.6-second gravity/fade cycle as the opening material shader.
  const fallPhase=(time,seed)=>(time/3600+seed)%1;
  const fallDistance=(phase,depth)=>{const age=phase*3.6;return depth*(.045*age+.18*age*age)/2.4948;};
  const fallOpacity=phase=>smooth(0,.025,phase)*(1-smooth(.55,1,phase));
  const allowed=()=>inView&&!document.hidden&&!document.body.classList.contains('opening-active')&&!document.body.classList.contains('portal-lesson')&&(bridging||!document.body.classList.contains('course-title-docking'));
  function stop(){cancelAnimationFrame(frame);frame=0;}
  function draw(now){
    const moving=animated();
    last=now;ctx.clearRect(0,0,width,height);
      for(const p of points){
        if(p.falling&&!moving)continue;
        let x=p.x,y=p.y,alpha=p.alpha,size=p.size;
        if(p.falling&&moving){
          const phase=fallPhase(now,p.seed);
          y+=fallDistance(phase,tail);
          x+=Math.sin(phase*4.2+p.seed*8)*phase*2.6;
          alpha*=fallOpacity(phase);size=Math.min(size,.88);
        }else{
          const phase=now*.00035+p.seed*6.28;
          const drift=moving?.18:0;
          x+=Math.sin(phase)*drift;y+=Math.cos(phase*.8)*drift;
        }
        ctx.globalAlpha=alpha;ctx.fillStyle=p.bright?'#f5e9cf':'#d9bd85';ctx.fillRect(x,y,size,size);
      }
      ctx.globalAlpha=1;
  }
  function paint(now){
    frame=0;if(!allowed()||!points.length)return;
    if(now-last>=32||!animated())try{draw(now);}catch(_){fallback();return;}
    if(animated())frame=requestAnimationFrame(paint);
  }
  function fallback(){stop();title.classList.remove('sand-title-ready');title.dataset.sandTitle='fallback';}
  function start(){
    stop();if(!points.length){fallback();return false;}
    // The bitmap must exist before CSS hides the accessible text or the flight
    // overlay disappears. A queued frame may be delayed behind a modal/resize.
    try{draw(performance.now());}catch(_){fallback();return false;}
    title.classList.add('sand-title-ready');title.dataset.sandTitle=animated()?'falling':'static';
    // Recheck the stable title, not a canvas whose observer may still report the
    // opening dialog's previous layout as offscreen.
    const box=title.getBoundingClientRect();inView=box.width>0&&box.height>0&&box.bottom+tail>0&&box.top<innerHeight;
    if(allowed()&&animated())frame=requestAnimationFrame(paint);
    return true;
  }
  function refresh(){
    queued=0;const box=title.getBoundingClientRect();if(!box.width||!box.height||!fontReady)return;
    const style=getComputedStyle(title),key=[box.width,box.height,title.lang,title.textContent,style.fontFamily,style.fontSize,style.letterSpacing,devicePixelRatio].join('|');
    if(key===geometryKey&&points.length)return start();
    stop();
    let ink;try{ink=window.CourseTitleDock.ink(title);}catch(_){fallback();return;}
    if(!ink.length){fallback();return;}
    width=box.width;tail=parseFloat(getComputedStyle(title).getPropertyValue('--sand-tail'))||150;height=box.height+tail;
    const ratio=Math.min(devicePixelRatio||1,2);canvas.width=Math.ceil(width*ratio);canvas.height=Math.ceil(height*ratio);ctx.setTransform(ratio,0,0,ratio,0,0);
    let seed=9281;const random=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed/4294967296;};
    const count=Math.min(innerWidth<600?8200:15000,ink.length*2);points=[];
    for(let i=0;i<count;i++){const p=ink[Math.floor(random()*ink.length)];points.push({x:p[0]-box.left,y:p[1]-box.top,size:.7+random()*.8,alpha:.62+random()*.38,bright:random()>.33,seed:random(),falling:random()<.23});}
    geometryKey=key;if(!canvas.isConnected)title.append(canvas);return start();
  }
  function schedule(){if(!queued)queued=requestAnimationFrame(refresh);}
  function prepareDock(){bridging=true;cancelAnimationFrame(queued);queued=0;refresh();}
  function finishDock(){bridging=false;return start();}
  new ResizeObserver(schedule).observe(title);
  new IntersectionObserver(entries=>{inView=entries[0].isIntersecting;if(inView)schedule();else stop();}).observe(title);
  new MutationObserver(records=>{if(records.some(r=>r.type==='characterData'))schedule();}).observe(title,{subtree:true,characterData:true});
  new MutationObserver(start).observe(document.body,{attributes:true,attributeFilter:['class']});
  window.addEventListener('course-sand-motion',start);
  window.addEventListener('course-language',schedule);document.addEventListener('visibilitychange',start);reduced.addEventListener('change',start);
  // Explicitly load the two title faces before sampling. Keep the painted glyph
  // shape when settings, focus or observers only change presentation state.
  Promise.all([document.fonts.load('400 88px CourseCalligraphy','代数学'),document.fonts.load('400 88px OpeningSerif','Algebra Ⅰ')]).then(()=>{fontReady=true;schedule();}).catch(()=>{fontReady=true;schedule();});
  window.CourseHeroSand={refresh:schedule,start,stop,prepareDock,finishDock,fallPhase,fallDistance,fallOpacity};schedule();
})();
