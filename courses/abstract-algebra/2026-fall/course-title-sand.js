/* The course title keeps a quiet sand surface after the opening has arrived. */
(()=>{
  const title=document.querySelector('.hero h1');if(!title)return;
  const reduced=matchMedia('(prefers-reduced-motion:reduce)');
  const canvas=document.createElement('canvas');canvas.className='course-hero-sand';canvas.setAttribute('aria-hidden','true');
  const ctx=canvas.getContext('2d');if(!ctx)return;
  let points=[],frame=0,last=0,queued=0,inView=true,width=0,height=0;
  const allowed=()=>inView&&!document.hidden&&!document.body.classList.contains('opening-active')&&!document.body.classList.contains('portal-lesson')&&!document.body.classList.contains('course-title-docking');
  function stop(){cancelAnimationFrame(frame);frame=0;}
  function paint(now){
    frame=0;if(!allowed()||!points.length)return;
    if(now-last>=32||reduced.matches){
      last=now;ctx.clearRect(0,0,width,height);
      for(const p of points){
        const phase=now*.00035+p.phase,motion=reduced.matches?0:1;
        const drift=p.drift*motion;
        ctx.globalAlpha=p.alpha*(.93+.07*Math.sin(phase));ctx.fillStyle=p.bright?'#f5e9cf':'#d9bd85';
        ctx.fillRect(p.x+Math.sin(phase)*drift,p.y+Math.cos(phase*.8)*drift*.55,p.size,p.size);
      }
      ctx.globalAlpha=1;
    }
    if(!reduced.matches)frame=requestAnimationFrame(paint);
  }
  function start(){stop();if(allowed()&&points.length)frame=requestAnimationFrame(paint);}
  function refresh(){
    queued=0;stop();const box=title.getBoundingClientRect();if(!box.width||!box.height)return;
    const ink=window.CourseTitleDock.ink(title);if(!ink.length){title.classList.remove('sand-title-ready');return;}
    width=box.width;height=box.height;const ratio=Math.min(devicePixelRatio||1,2);
    canvas.width=Math.ceil(width*ratio);canvas.height=Math.ceil(height*ratio);ctx.setTransform(ratio,0,0,ratio,0,0);
    let seed=9281;const random=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed/4294967296;};
    const count=Math.min(innerWidth<600?6000:10500,ink.length);points=[];
    for(let i=0;i<count;i++){const p=ink[Math.floor(random()*ink.length)];points.push({x:p[0]-box.left,y:p[1]-box.top,size:.7+random()*.85,alpha:.55+random()*.45,bright:random()>.33,phase:random()*Math.PI*2,drift:random()<.035?2.5+random()*2:.12+random()*.24});}
    if(!canvas.isConnected)title.append(canvas);title.classList.add('sand-title-ready');title.dataset.sandTitle='ready';last=0;start();
  }
  function schedule(){if(!queued)queued=requestAnimationFrame(refresh);}
  new ResizeObserver(schedule).observe(title);
  new IntersectionObserver(entries=>{inView=entries[0].isIntersecting;if(inView)schedule();else stop();}).observe(title);
  new MutationObserver(records=>{if(records.some(r=>r.type==='characterData'))schedule();}).observe(title,{subtree:true,characterData:true});
  new MutationObserver(start).observe(document.body,{attributes:true,attributeFilter:['class']});
  window.addEventListener('course-language',schedule);document.addEventListener('visibilitychange',start);reduced.addEventListener('change',start);
  document.fonts.addEventListener('loadingdone',schedule);document.fonts.ready.then(schedule);
  window.CourseHeroSand={refresh:schedule,start,stop};schedule();
})();
