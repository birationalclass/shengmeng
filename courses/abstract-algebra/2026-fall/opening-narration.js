/* Left-hand narration shares the ring's type scale and paginates long passages.
   Explicit language selection stays fixed; callers without a preference retain
   the legacy English-then-Chinese sequence. */
(() => {
  'use strict';
  function paginate(text,fits,language){
    const characters=Array.from(text),pages=[];let start=0;
    while(start<characters.length){
      let low=start+1,high=characters.length,end=low;
      while(low<=high){const middle=(low+high)>>1;if(fits(characters.slice(start,middle).join('').trim())){end=middle;low=middle+1;}else high=middle-1;}
      if(end<characters.length&&language==='en'){
        let boundary=end;while(boundary>start&&!/\s/.test(characters[boundary-1]))boundary--;
        if(boundary>start+(end-start)/2)end=boundary;
      }
      pages.push(characters.slice(start,end).join(''));start=end;
    }
    return pages.length?pages:[''];
  }
  window.CourseOpeningNarration={paginate,create(element,scenes,options={}){
    let scene=-1,cycle=0,language='en',phase='reading',elapsed=0,target='zh',fadeElapsed=0;
    let pages=[''],page=0,pageElapsed=0,layoutPending=false;
    let preferred=options.language==='en'?'en':options.language==='zh'?'zh':null;
    const chineseOnly=()=>scene>=0&&scenes[scene].language==='zh';
    const initialLanguage=()=>preferred||(chineseOnly()?'zh':'en');
    const clearFade=()=>{element.classList.remove('is-language-changing');element.classList.remove('is-page-changing');};
    function layout(){
      const item=scenes[scene],full=(item.verse||item)[language]||'';
      const offset=pages.slice(0,page).join('').length;pages=[full];
      if(element.setAttribute)element.setAttribute('aria-label',full);
      // The ring's four-line verse keeps its original uninterrupted delivery.
      if(element.ownerDocument&&item.kind!=='ring-verse'){
        const measure=element.cloneNode(false);measure.removeAttribute('aria-label');measure.setAttribute('aria-hidden','true');
        Object.assign(measure.style,{position:'absolute',inset:'0 auto auto 0',width:'100%',visibility:'hidden',opacity:'0',transform:'none',transition:'none',maxHeight:'var(--narration-page-height)',pointerEvents:'none'});
        element.parentElement.appendChild(measure);
        const limit=parseFloat(getComputedStyle(measure).maxHeight);measure.style.maxHeight='none';
        if(limit>0)pages=paginate(full,text=>{measure.textContent=text;return measure.getBoundingClientRect().height<=limit+.5;},language);
        measure.remove();
      }
      page=0;let consumed=0;while(page<pages.length-1&&consumed+pages[page].length<=offset){consumed+=pages[page].length;page++;}
      if(phase==='paging'){phase='reading';pageElapsed=0;clearFade();}
      element.textContent=pages[page].trim();
      element.dataset.page=String(page+1);element.dataset.pages=String(pages.length);layoutPending=false;
    }
    function render(){
      const item=scenes[scene];element.lang=language==='zh'?'zh-CN':'en';element.dataset.kind=item.kind||'quote';
      pages=[''];page=0;pageElapsed=0;layout();clearFade();
    }
    function fadeTo(next){target=next;phase='fading';fadeElapsed=0;element.classList.remove('is-page-changing');element.classList.add('is-language-changing');}
    function setScene(index,currentCycle=0){
      if(index!==scene){scene=index;cycle=currentCycle;language=initialLanguage();phase='reading';elapsed=0;render();}
      else if(currentCycle!==cycle){
        cycle=currentCycle;
        if(language!==initialLanguage())fadeTo(initialLanguage());
        else{phase='reading';elapsed=0;render();}
      }
    }
    if(element.ownerDocument){
      const root=element.closest('#symmetry-particle-studies');
      const reflow=()=>{if(scene>=0)layout();};
      if(root&&typeof ResizeObserver!=='undefined')new ResizeObserver(reflow).observe(root);
      if(root&&typeof MutationObserver!=='undefined')new MutationObserver(reflow).observe(root,{attributes:true,attributeFilter:['style','class']});
    }
    function tick(dt,shown,{fadeMs=2400,holdEnglish=false,englishMs=8000}={}){
      if(scene<0||!shown)return;
      if(layoutPending)layout();
      if(!preferred&&!chineseOnly()&&holdEnglish&&language!=='en'&&(phase!=='fading'||target!=='en'))fadeTo('en');
      if(phase==='fading'){
        if(language==='en'&&target==='zh'&&holdEnglish){phase='reading';clearFade();return;}
        fadeElapsed+=dt;
        if(fadeElapsed>=fadeMs){language=target;phase='reading';elapsed=0;render();}
      }else if(phase==='paging'){
        fadeElapsed+=dt;
        if(fadeElapsed>=Math.min(600,fadeMs)){page=Math.min(page+1,pages.length-1);pageElapsed=0;phase='reading';element.textContent=pages[page].trim();element.dataset.page=String(page+1);clearFade();}
      }else{
        elapsed+=dt;pageElapsed+=dt;
        const pageHold=language==='en'?englishMs/pages.length:Math.min(4000,10000/pages.length);
        if(page<pages.length-1&&pageElapsed>=pageHold){phase='paging';fadeElapsed=0;element.classList.add('is-page-changing');}
        else if(!preferred&&!chineseOnly()&&language==='en'&&page===pages.length-1&&elapsed>=englishMs&&pageElapsed>=(pages.length>1?pageHold:0)&&!holdEnglish)fadeTo('zh');
      }
    }
    return{setScene,tick,setLanguage(value){preferred=value==='en'?'en':'zh';language=preferred;phase='reading';elapsed=0;if(scene>=0)render();},reset(){scene=-1;phase='reading';clearFade();},get language(){return language;},get needsFrames(){return scene>=0&&(layoutPending||page<pages.length-1||phase!=='reading'||(!preferred&&!chineseOnly()&&language==='en'));}};
  }};
})();
