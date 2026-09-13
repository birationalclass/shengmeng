const assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),vm=require('node:vm');
const window={};vm.runInNewContext(fs.readFileSync(path.join(__dirname,'..','opening-galois-timeline.js'),'utf8'),{window});
const sample=window.CourseOpeningGaloisTimeline.sample;
for(const [elapsed,year] of [[0,1811],[7000,1811],[11000,1827],[24000,1831],[92500,1832],[133500,1832],[143000,1832],[166000,1843],[168200,1843],[169000,1846],[177160.612,1846]])assert.equal(sample({elapsed}).displayYear,year);
assert.equal(sample({elapsed:6999}).birth,true);assert.equal(sample({elapsed:7000}).birth,false);
assert.equal(sample({elapsed:124549}).death,false);assert.equal(sample({elapsed:124550}).death,true);assert.equal(sample({elapsed:133499}).death,true);assert.equal(sample({elapsed:133500}).death,false);
assert.equal(sample({elapsed:128000}).position,.6,'the death anchor is fixed at 1832 on the 1811–1846 scale');
const entering=sample({entering:true,elapsed:128000});assert.equal(entering.displayYear,1811);assert.equal(entering.birth,false);assert.equal(entering.death,false);
let previous=1811;for(let elapsed=0;elapsed<=177160;elapsed+=500){const s=sample({elapsed});assert(s.year>=previous&&s.year<=1846);assert(s.position>=0&&s.position<=1);previous=s.year;assert.equal(sample({elapsed}).year,s.year,'the same playback time renders identically when reversing');}
assert.equal(sample({elapsed:200000}).displayYear,1846);assert.equal(sample({elapsed:-1}).displayYear,1811);
console.log('PASS: Galois historical scale, birth/death dwell, final reception dates, entry state and reversible time');
