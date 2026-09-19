/* Course UI labels and shared title geometry; narration has its own language. */
(()=>{
  'use strict';
  const en=()=>window.CourseLanguage?.language==='en';
  const t=(zh,english)=>en()?english:zh;
  window.CourseLanguage.add({'加载背景音乐':'Loading music','准备中英文字体':'Preparing Chinese and English fonts','准备沙粒动画':'Preparing the sand animation','音乐加载未完成，请重试':'Music could not finish loading. Please retry.','字体加载未完成，请重试':'Fonts could not finish loading. Please retry.','点击或按空格 / 回车 · 重新加载':'Click, Space or Enter · retry','准备完成':'Ready','生成图形':'Building shapes','准备沙粒':'Preparing grains','准备呈现':'Preparing the scene','即将到来':'Upcoming'});
  function labels(){
    // The animation controller owns its independent narration-language button.
    const copy={'.loading-hint':['正在准备动画','Preparing the animation'],'.ready-hint':['点击或按空格 / 回车，开始动画','Click, Space or Enter · start animation'],'.galois-hint':['按空格或回车跳过伽罗瓦终章','Space or Enter · skip the Galois epilogue'],'.touch-hint':['右下角可跳至伽罗瓦终章','Use the lower-right button to skip to Galois']};
    for(const [selector,pair] of Object.entries(copy)){const el=document.querySelector('#courseOpening '+selector);if(el)el.textContent=t(...pair);}
    document.querySelector('.hero h1')?.setAttribute('lang',en()?'en':'zh-CN');
    document.querySelector('.course-author')?.setAttribute('lang',en()?'en':'zh-CN');
  }
  window.addEventListener('course-language',labels);labels();
  const smooth=x=>{x=Math.max(0,Math.min(1,x));return x*x*(3-2*x);};
  function project(x,y,width,height){
    const aspect=width/height,fit=Math.min(.68,aspect*.84),centre=.05+.15*smooth((aspect-.8)/.5);
    return [width/2+x*fit*height/2,height/2-(y*fit+centre)*height/2];
  }
  function ink(element){
    const box=element.getBoundingClientRect(),width=Math.ceil(box.width),height=Math.ceil(box.height);if(!width||!height)return [];const canvas=document.createElement('canvas');canvas.width=width;canvas.height=height;
    const ctx=canvas.getContext('2d',{willReadFrequently:true}),walker=document.createTreeWalker(element,NodeFilter.SHOW_TEXT);let node;
    ctx.fillStyle='#fff';
    while(node=walker.nextNode()){
      if(!node.data.trim())continue;
      const range=document.createRange();range.selectNodeContents(node);const r=range.getBoundingClientRect(),style=getComputedStyle(node.parentElement);
      ctx.font=`${style.fontStyle} ${style.fontWeight} ${style.fontSize} ${style.fontFamily}`;
      if('letterSpacing' in ctx)ctx.letterSpacing=style.letterSpacing==='normal'?'0px':style.letterSpacing;
      const m=ctx.measureText(node.data),ascent=m.fontBoundingBoxAscent??m.actualBoundingBoxAscent,descent=m.fontBoundingBoxDescent??m.actualBoundingBoxDescent;
      ctx.fillText(node.data,r.left-box.left,r.top-box.top+(r.height-ascent-descent)/2+ascent);
    }
    const pixels=ctx.getImageData(0,0,width,height).data,points=[];
    for(let y=0;y<height;y++)for(let x=0;x<width;x++)if(pixels[(y*width+x)*4+3]>72)points.push([x+box.left,y+box.top]);
    return points;
  }
  let cancel=()=>{};
  function dock(geometry,leave){
    cancel();
    const title=document.querySelector('.hero h1');
    if(!title){leave();return;}
    const fromSize={width:innerWidth,height:innerHeight};
    document.body.classList.add('course-title-docking');leave();
    window.scrollTo({top:0,left:0,behavior:'instant'});
    document.getElementById('course-scroll-region')?.scrollTo({top:0,left:0,behavior:'instant'});
    window.CourseHeroSand?.prepareDock();
    let targets;try{targets=[ink(title)];}catch(_){targets=[[]];}
    const heroTail=parseFloat(getComputedStyle(title).getPropertyValue('--sand-tail'))||150;
    if(targets.some(points=>!points.length)){window.CourseHeroSand?.finishDock();document.body.classList.remove('course-title-docking');document.body.dataset.titleFlight='complete';return;}
    const overlay=document.createElement('canvas');overlay.className='course-title-flight';overlay.setAttribute('aria-hidden','true');document.body.append(overlay);
    const ratio=Math.min(devicePixelRatio||1,2),width=innerWidth,height=innerHeight;overlay.width=width*ratio;overlay.height=height*ratio;
    const ctx=overlay.getContext('2d');ctx.scale(ratio,ratio);
    const n=geometry.positions.length/3,stride=Math.max(1,Math.ceil(n/5500)),particles=[];
    let seed=731;const random=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed/4294967296;};
    for(let i=0;i<n;i+=stride){if(geometry.signatureWeights[i]>.5)continue;const point=targets[0][Math.floor(random()*targets[0].length)],start=project(geometry.positions[i*3],geometry.positions[i*3+1],fromSize.width,fromSize.height);particles.push({x:start[0],y:start[1],tx:point[0],ty:point[1],curve:(random()-.5)*100,delay:random()*.14,size:.65+random()*.75,falling:random()<.23,seed:random()});}
    let frame=0,start=0,done=false;const reduced=matchMedia('(prefers-reduced-motion:reduce)').matches,duration=reduced?220:2200;
    document.body.dataset.titleFlight='moving';
    function finish(){
      if(done)return;done=true;cancelAnimationFrame(frame);
      // Commit a painted destination before removing the moving particles.
      // If drawing fails, the readable title remains as a fallback.
      try{window.CourseHeroSand?.finishDock();}catch(_){title.classList.remove('sand-title-ready');}
      overlay.remove();title.style.removeProperty('opacity');document.body.classList.remove('course-title-docking');document.body.dataset.titleFlight='complete';
      window.removeEventListener('resize',finish);window.removeEventListener('pointerdown',finish);window.removeEventListener('wheel',finish);window.removeEventListener('keydown',onKey);
    }
    function onKey(event){if(event.key==='Escape')finish();}
    cancel=finish;window.addEventListener('resize',finish,{once:true});window.addEventListener('pointerdown',finish,{once:true});window.addEventListener('wheel',finish,{once:true});window.addEventListener('keydown',onKey);
    function paint(now){
      if(done)return;if(!start)start=now;const t=Math.min(1,(now-start)/duration);
      ctx.clearRect(0,0,width,height);ctx.fillStyle=`rgba(17,16,13,${1-smooth(t/.4)})`;ctx.fillRect(0,0,width,height);
      ctx.fillStyle='#dec593';ctx.globalAlpha=t>.88?1-smooth((t-.88)/.12):1;
      for(const p of particles){
        const u=reduced?1:smooth(Math.max(0,(t-p.delay)/(1-p.delay))),curve=Math.sin(Math.PI*u)*p.curve;
        let y=p.y+(p.ty-p.y)*u-curve*.35,alpha=t>.88?1-smooth((t-.88)/.12):1,size=p.size;
        if(p.falling&&!reduced&&document.documentElement.dataset.sandMotion!=='off'&&window.CourseHeroSand){const phase=window.CourseHeroSand.fallPhase(now,p.seed);y+=window.CourseHeroSand.fallDistance(phase,fromSize.height*.65*(1-u)+heroTail*u);alpha*=window.CourseHeroSand.fallOpacity(phase);size=Math.min(size,.9);}
        ctx.globalAlpha=alpha;ctx.fillRect(p.x+(p.tx-p.x)*u+curve,y,size,size);
      }
      ctx.globalAlpha=1;if(t>.88){title.style.opacity=String(smooth((t-.88)/.12));}
      if(t<1)frame=requestAnimationFrame(paint);else{title.style.removeProperty('opacity');finish();}
    }
    frame=requestAnimationFrame(paint);
  }
  window.CourseTitleDock=Object.freeze({start:dock,project,ink,cancel:()=>cancel(),label:()=>t('代数学 Ⅰ。孟晟。','Algebra Ⅰ. Sheng Meng.'),text:t});
})();
