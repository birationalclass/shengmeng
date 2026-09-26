// Mathematical symbols in prose use a local print face, never the chalk font.
// Formulas themselves remain MathJax SVG outlines.
const printed=/([\p{Script=Latin}\p{Number}\u1d00-\u1dbf\u0300-\u036f\u0370-\u03ff\u2070-\u209f\u2100-\u214f\u2190-\u22ff\u{1d400}-\u{1d7ff}§.,:;=+<>()[\]{}^_−/]+)/gu;
export const mathFont='RefugeMath, "Times New Roman", serif';
export function chalkRuns(text){const runs=[];for(const part of String(text).split(printed).filter(Boolean)){const math=printedTest(part),last=runs.at(-1);if(last&&last.math===math)last.text+=part;else runs.push({text:part,math});}return runs;}
function printedTest(text){
  const core=text.replace(/^[()[\]{}.,:;]+|[()[\]{}.,:;]+$/g,'');
  const symbols=/[\p{Number}\u1d00-\u1dbf\u0370-\u03ff\u2070-\u209f\u2100-\u214f\u2190-\u22ff\u{1d400}-\u{1d7ff}§=+<>^_−/]/u;
  if(symbols.test(core))return true;
  // Ordinary English words (including accented names) remain handwriting.
  // Bare variables are print; English articles/pronouns a, A and I are prose.
  if(/^[\p{Script=Latin}\p{Mark}]+$/u.test(core))return [...core].length===1&&!/^[aAI]$/.test(core);
  return /[A-Za-z].*[()[\]{}]|[()[\]{}].*[A-Za-z]/.test(core);
}
const escape=text=>text.replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
// Parse simple TeX scripts in prose once for canvas, HTML and SVG output.
// Keep prose classification separate so ordinary English stays handwritten.
export function chalkInlineRuns(text){
  return chalkRuns(text).flatMap(run=>{
    if(!run.math)return [run];
    const parts=[];let at=0;
    for(const match of run.text.matchAll(/([_^])(?:\{([^{}]+)\}|([A-Za-z0-9]))/g)){
      if(match.index>at)parts.push({text:run.text.slice(at,match.index),math:true});
      parts.push({text:match[2]||match[3],math:true,script:match[1]==='_'?'sub':'sup'});at=match.index+match[0].length;
    }
    if(at<run.text.length)parts.push({text:run.text.slice(at),math:true});return parts;
  });
}
export function chalkHTML(text){return chalkInlineRuns(text).map(run=>{
  const content=escape(run.text),body=run.script?`<${run.script}>${content}</${run.script}>`:content;
  return run.math?`<span class="chalk-math">${body}</span>`:body;
}).join('');}
export function chalkSVG(text,{heading=false}={}){return chalkInlineRuns(text).map(run=>{
  const attrs=run.script?` font-size="70%" baseline-shift="${run.script}"`:'';
  return run.math&&!(heading&&/^\d+(?:\.\d+)*[.)]?$/.test(run.text))?`<tspan font-family="Times New Roman, serif"${attrs}>${escape(run.text)}</tspan>`:escape(run.text);
}).join('');}
