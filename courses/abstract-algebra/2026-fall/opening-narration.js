/* Left-hand narration: English first, then Chinese, with a complete fade between. */
(() => {
  'use strict';
  window.CourseOpeningNarration={create(element,scenes){
    let scene=-1,cycle=0,language='en',phase='reading',elapsed=0,target='zh',fadeElapsed=0;
    function render(){
      const item=scenes[scene],text=item.verse||item;
      element.textContent=text[language]||'';element.lang=language==='zh'?'zh-CN':'en';
      element.dataset.kind=item.kind||'quote';element.classList.remove('is-language-changing');
    }
    function fadeTo(next){target=next;phase='fading';fadeElapsed=0;element.classList.add('is-language-changing');}
    function setScene(index,currentCycle=0){
      if(index!==scene){scene=index;cycle=currentCycle;language='en';phase='reading';elapsed=0;render();}
      else if(currentCycle!==cycle){
        cycle=currentCycle;
        if(language!=='en')fadeTo('en');
        else{phase='reading';elapsed=0;element.classList.remove('is-language-changing');}
      }
    }
    function tick(dt,shown,{fadeMs=2400,holdEnglish=false}={}){
      if(scene<0||!shown)return;
      if(holdEnglish&&language!=='en'&&(phase!=='fading'||target!=='en'))fadeTo('en');
      if(phase==='fading'){
        if(language==='en'&&target==='zh'&&holdEnglish){phase='reading';element.classList.remove('is-language-changing');return;}
        fadeElapsed+=dt;
        if(fadeElapsed>=fadeMs){language=target;phase='reading';elapsed=0;render();}
      }else if(language==='en'){
        elapsed+=dt;
        if(elapsed>=8000&&!holdEnglish)fadeTo('zh');
      }
    }
    return{setScene,tick,reset(){scene=-1;phase='reading';element.classList.remove('is-language-changing');},get language(){return language;},get needsFrames(){return scene>=0&&(language==='en'||phase==='fading');}};
  }};
})();
