import {chalkHTML} from './chalk-typography.js?v=30-seminar';
import {controlLabel} from './control-label.js?v=22-handwritten-cover';
import {readingFormulaWidth} from './display-profile.js?v=8-cover';

// The reading layer uses vector formulas and real HTML text, not a magnified
// screenshot of the 3D texture. The six physical boards remain in the scene.
export function createChalkReader(lecture){
  const $=id=>document.getElementById(id),panel=$('chalkReader');
  let page=-1,reportId='',language='',teaching=false,lastPlaying=null;
  function show(open){panel.hidden=!open;$('readerOpen').setAttribute('aria-expanded',String(open));if(open){$('lecturePanel').hidden=true;$('lectureButton').setAttribute('aria-expanded','false');update();}}
  function size(){
    const px=Number($('readerFont').value),entry=lecture.pages[lecture.clock.page];
    $('readerFormula').style.width=readingFormulaWidth(entry.formulaEm,px)+'px';
    $('readerExplanation').style.fontSize=Math.max(16,px*.75)+'px';
    $('readerFontValue').textContent=px+' px';
  }
  function update(){
    if(panel.hidden)return;
    if(page!==lecture.clock.page||language!==lecture.language||reportId!==lecture.report?.id){
      reportId=lecture.report?.id;
      page=lecture.clock.page;language=lecture.language;const entry=lecture.pages[page],copy=lecture.copy?.(page)||entry;
      $('readerSection').textContent=`${copy.source} · ${page+1} / ${lecture.pages.length}`;
      $('readerTitle').textContent=copy.title;$('readerExplanation').textContent=copy.text;
      $('readerAuthor').hidden=entry.kind!=='cover';$('readerAuthor').textContent=copy.author||'';$('readerFormulaViewport').hidden=Boolean(entry.kind);
      $('readerTitle').innerHTML=chalkHTML(copy.title);$('readerExplanation').innerHTML=chalkHTML(copy.text)+(entry.annotation?.label?'<br><span style="color:#d9c693">↳ '+chalkHTML(entry.annotation.label[language])+'</span>':'');
      for(const id of ['readerTitle','readerExplanation'])$(id).style.fontFamily=language==='en'?'RefugeLatin, cursive':'RefugeChinese, cursive';
      $('readerFormula').alt=entry.tex;$('readerFormula').src=entry.formulaAsset+'?v=32-report-position';
      $('readerFormula').hidden=false;$('readerError').hidden=true;
      $('readerFormulaViewport').scrollLeft=0;size();
    }
    $('readerPlay').disabled=Boolean(lecture.clock.ended);$('readerNext').disabled=lecture.clock.page===lecture.pages.length-1;$('readerPrevious').disabled=lecture.clock.page===0;
    if(lastPlaying!==lecture.playing){lastPlaying=lecture.playing;controlLabel($('readerPlay'),lecture.clock.ended?'报告已结束':lecture.playing?'暂停翻页':'继续翻页');$('readerPlay').setAttribute('aria-pressed',String(lecture.playing));}
  }
  $('readerOpen').addEventListener('click',()=>show(panel.hidden));
  $('readerClose').addEventListener('click',()=>show(false));
  $('readerFont').addEventListener('input',size);
  $('readerPrevious').addEventListener('click',()=>$('lecturePrevious').click());
  $('readerNext').addEventListener('click',()=>$('lectureNext').click());
  $('readerPlay').addEventListener('click',()=>$('lecturePlay').click());
  $('readerFormula').addEventListener('error',()=>{$('readerFormula').hidden=true;$('readerError').hidden=false;});
  return {update,close:()=>show(false),chapter(active,allowAuto=true){
    // Open once on entry to the teaching chapter on a small screen. Dismissing
    // the reader stays respected while pausing or adjusting that same chapter.
    if(active&&!teaching&&allowAuto&&Math.min(innerWidth,innerHeight)<=700)show(true);
    if(!active&&teaching)show(false);teaching=active;
  }};
}
