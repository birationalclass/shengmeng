// Mathematical symbols in prose use a local print face, never the chalk font.
// Formulas themselves remain MathJax SVG outlines.
const printed=/([\p{Script=Latin}\p{Number}\u1d00-\u1dbf\u0300-\u036f\u0370-\u03ff\u2070-\u209f\u2100-\u214f\u2190-\u22ff\u{1d400}-\u{1d7ff}§.,:;=+<>()[\]{}^_−/]+)/gu;
export const mathFont='RefugeMath, "Times New Roman", serif';
export function chalkRuns(text){return String(text).split(printed).filter(Boolean).map(text=>({text,math:printedTest(text)}));}
function printedTest(text){printed.lastIndex=0;const yes=printed.test(text);printed.lastIndex=0;return yes;}
const escape=text=>text.replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
export function chalkHTML(text){return chalkRuns(text).map(run=>run.math?`<span class="chalk-math">${escape(run.text)}</span>`:escape(run.text)).join('');}

export function chalkSVG(text){return chalkRuns(text).map(run=>run.math?`<tspan font-family="Times New Roman, serif">${escape(run.text)}</tspan>`:escape(run.text)).join('');}
