const assert=require('node:assert/strict'),fs=require('node:fs'),vm=require('node:vm'),path=require('node:path');
const window={};vm.runInNewContext(fs.readFileSync(path.join(__dirname,'../opening-materials.js'),'utf8'),{window});
const {mineralKind}=window.CourseOpeningMaterials,all=[true,true,true,true,true,true],samples=100000;
function counts(share,enabled=all){const out=Array(6).fill(0);for(let i=0;i<samples;i++){const kind=mineralKind((i+.5)/samples,enabled,share);if(kind>=0)out[kind]++;}return out;}
for(const fraction of [0,.005,.015,.05]){const n=counts(fraction);assert.equal(n.slice(1).reduce((a,b)=>a+b,0),samples*fraction);for(let i=1;i<6;i++)assert.equal(n[i],samples*fraction/5);}
const fewer=[true,true,false,true,true,true],many=counts(.05),filtered=counts(.05,fewer);
assert.equal(filtered[2],0);for(const i of [1,3,4,5])assert.equal(filtered[i],many[i],'disabled stones do not redistribute their share');
for(let i=0;i<samples;i++){const seed=(i+.5)/samples,k=mineralKind(seed,all,.005);if(k)assert.equal(mineralKind(seed,all,.05),k,'raising the amount preserves each existing stone and species');}
console.log('PASS: 0–5% gemstone density, five equal species, stable seeds, independent selections');
