const assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),vm=require('node:vm');
const window={};vm.runInNewContext(fs.readFileSync(path.join(__dirname,'../opening-narration.js'),'utf8'),{window});
const paginate=window.CourseOpeningNarration.paginate;
for(const [text,language] of [
 ['Triangle Groups\nUp to similarity, there are exactly five convex regular polyhedra.\n\nΔ⁺(2,3,3) ≅ A₄: tetrahedron','en'],
 ['三角群\n在三维欧氏空间中，凸正多面体按相似分类恰有五种。\n\nΔ⁺(2,3,3) ≅ A₄：四面体','zh']]){
 const pages=paginate(text,s=>s.length<=32,language);
 assert(pages.length>1);assert.equal(pages.join(''),text,'pagination must retain every word and formula');
 assert(pages.every(s=>s.trim().length<=32),'all pages fit without reducing type size');
}
const complete='God’s Fingerprint\nThe Art of Iteration';assert.deepEqual(Array.from(paginate(complete,()=>true,'en')),[complete]);
console.log('PASS: long narration retains all text at fixed type size; short passages stay intact');
