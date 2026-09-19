const assert=require('node:assert/strict'),fs=require('node:fs'),vm=require('node:vm'),path=require('node:path');
const context={window:{}};context.self=context.window;vm.runInNewContext(fs.readFileSync(path.join(__dirname,'../../../../study/spectral/vendor/katex.min.js'),'utf8'),context);for(const name of ['math-format','content','chapter-two','exercises','textbook-references'])vm.runInNewContext(fs.readFileSync(path.join(__dirname,name+'.js'),'utf8'),context);
const {inline}=context.window.GroupLessonMath;
assert.equal(inline('0≤r<n；i<j；|G|>1'), '0≤r&lt;n；i&lt;j；|G|&gt;1');
for(const text of ['C_G(a)','λ_(g⁻¹)','λ_(gh)','C_D₃(r)']){assert.match(inline(text),/class="katex"/);assert.doesNotMatch(inline(text),/katex-error/);}
assert.match(inline('<img src=x>'),/&lt;img src=x&gt;/);
let strings=0;function inspect(value){if(typeof value==='string'){inline(value);strings++;}else if(value&&typeof value==='object')Object.values(value).forEach(inspect)}
for(const book of Object.values(context.window.GroupCourseContent))for(const entry of book.entries){for(const key of ['text','proof','example','warning','extraProof'])inspect(entry[key]);const ref=context.window.GroupTextbookReferences[book.id][entry.id];assert(ref&&ref.label.length===2&&ref.pdfPages.length);assert.notEqual(ref.label[0],'§'+book.id);}
inspect(context.window.GroupCourseExercises);
assert.equal(context.window.GroupTextbookReferences['2.5'].action.label[0],'定义 2.5.1');
assert.equal(context.window.GroupTextbookReferences['1.3'].finite.label[0],'习题 1-3 · 第 15 题');
console.log('PASS:',strings,'prose strings render; inequalities preserved; textbook references cover every entry');
