const assert=require('node:assert/strict');
require('../opening-inscription.js');
const I=globalThis.CourseOpeningInscription;
// All portrait layouts retain their original rendering, including tablet widths.
for(const [w,h] of [[390,844],[430,932],[768,1024],[1000,1000]]){assert.equal(I.scale(w,h),1);assert.equal(I.signatureScale(w,h),1);}
for(const [w,h] of [[1280,800],[1920,1080],[2560,1440]])assert.equal(I.signatureScale(w,h),.35);
for(const [w,h] of [[0,900],[1440,0],[Infinity,900],[NaN,900]])assert.equal(I.scale(w,h),1);
// On a full landscape display, grain diameter relative to projected glyph size
// matches the existing 390 × 844 phone reference, at every tested resolution.
const reference=(844/800)/(390*.84);
for(const [w,h] of [[1280,800],[1440,900],[1920,1080],[2560,1440],[3840,2160]]){
  const actual=I.scale(w,h)*Math.max(1,Math.min(1.4,h/800))/(h*Math.min(.68,w/h*.84));
  assert.ok(Math.abs(actual-reference)<1e-12);
}
for(const aspect of [1,1.3]){
  const delta=I.scale((aspect+.000001)*900,900)-I.scale((aspect-.000001)*900,900);
  assert.ok(Math.abs(delta)<1e-9,'orientation breakpoints have no abrupt size change');
}
const p=I.create(3),portrait=new Float32Array(9),figure=new Float32Array(9),closing=new Float32Array(9);
const text=new Float32Array([0,1,1]);p.mark(portrait,text,text);p.mark(closing,undefined,new Float32Array([0,0,1]));
p.update(portrait,figure);assert.deepEqual([...p.attributes],[0,0,0,0,1,0,1,0,1,0,1,0]);
assert.equal(p.update(portrait,figure),false,'steady figures reuse the same attribute buffer');
const capture=new Float32Array(9);p.capture(portrait,figure,.25,capture);
p.update(capture,closing);assert.deepEqual([...p.attributes],[0,1,0,0,.75,1,.75,0,.75,1,.75,1],'interrupted morph retains each grain’s text and fine-lettering weights');
const second=new Float32Array(9);p.capture(capture,closing,.4,second);
p.update(second,figure);
for(const [i,value] of [.4,.85,.85].entries())assert.ok(Math.abs(p.attributes[4*i]-value)<1e-6);
for(const [i,value] of [0,.45,.85].entries())assert.ok(Math.abs(p.attributes[4*i+2]-value)<1e-6);
p.update(figure,figure);assert.ok(p.attributes.every(v=>v===0),'ordinary sand scenes are unaffected');
console.log('PASS: phone preserved, landscape names use fine grains, Algebra separately masked, resize and interrupted morphs continuous');
