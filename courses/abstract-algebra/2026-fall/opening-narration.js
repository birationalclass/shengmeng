/* Left-hand narration: bilingual by default; a scene can stay in Chinese. */
(() => {
  'use strict';
  window.CourseOpeningNarration={create(element,scenes){
    let scene=-1,cycle=0,language='en',phase='reading',elapsed=0,target='zh',fadeElapsed=0;
    const chineseOnly=()=>scene>=0&&scenes[scene].language==='zh';
    const initialLanguage=()=>chineseOnly()?'zh':'en';
    function render(){
      const item=scenes[scene],text=item.verse||item;
      element.textContent=text[language]||'';element.lang=language==='zh'?'zh-CN':'en';
      element.dataset.kind=item.kind||'quote';element.classList.remove('is-language-changing');
    }
    function fadeTo(next){target=next;phase='fading';fadeElapsed=0;element.classList.add('is-language-changing');}
    function setScene(index,currentCycle=0){
      if(index!==scene){scene=index;cycle=currentCycle;language=initialLanguage();phase='reading';elapsed=0;render();}
      else if(currentCycle!==cycle){
        cycle=currentCycle;
        if(language!==initialLanguage())fadeTo(initialLanguage());
        else{phase='reading';elapsed=0;element.classList.remove('is-language-changing');}
      }
    }
    function tick(dt,shown,{fadeMs=2400,holdEnglish=false,englishMs=8000}={}){
      if(scene<0||!shown)return;
      if(chineseOnly())return;
      if(holdEnglish&&language!=='en'&&(phase!=='fading'||target!=='en'))fadeTo('en');
      if(phase==='fading'){
        if(language==='en'&&target==='zh'&&holdEnglish){phase='reading';element.classList.remove('is-language-changing');return;}
        fadeElapsed+=dt;
        if(fadeElapsed>=fadeMs){language=target;phase='reading';elapsed=0;render();}
      }else if(language==='en'){
        elapsed+=dt;
        if(elapsed>=englishMs&&!holdEnglish)fadeTo('zh');
      }
    }
    return{setScene,tick,reset(){scene=-1;phase='reading';element.classList.remove('is-language-changing');},get language(){return language;},get needsFrames(){return scene>=0&&!chineseOnly()&&(language==='en'||phase==='fading');}};
  }};
})();
