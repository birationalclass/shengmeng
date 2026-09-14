/* The approved Mac ink must be identical without any installed fonts. */
'use strict';
const assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),crypto=require('node:crypto');
const base=path.resolve(__dirname,'..');
const context=vm.createContext({
  window:{},atob:s=>Buffer.from(s,'base64').toString('binary'),
  document:{createElement(tag){
    assert.equal(tag,'canvas');
    return {getContext(){return {
      setTransform(){},
      getImageData(){throw new Error('Fixed artwork must not rasterize canvas text');}
    };}};
  }}
});
for(const name of['opening-lettering-data.js','opening-galois-portrait.js','opening-galois.js','opening-outro.js'])vm.runInContext(fs.readFileSync(path.join(base,name),'utf8'),context,{filename:name});
const data=context.window.CourseOpeningLetteringData;
assert.equal(data.source,'approved-mac-20260914');
for(const[name,count]of Object.entries({galoisTitle:11708,galoisDates:2734,outro:68507})){
  const pixels=data.pixels(name);assert.equal(pixels.length,count);assert.equal(data.pixels(name),pixels);
  for(let i=1;i<pixels.length;i++)assert.ok(pixels[i]>pixels[i-1],'Pixel order determines particle correspondence');
}
assert.equal(data.publicationAlpha().length,1400*1400);
assert.throws(()=>data.pixels('missing'),/Missing fixed/);
assert.throws(()=>data.pixels('publication'),/requires alpha/);
const expected={"galois":{"positions":"1e85ba498663fac1f379cabaccd0fb819a2bbd35735bc9908460d4a33ce15028","normals":"1491264f836fcbc91d231fd11744c6dddcfe38468e50b62e2e954bac8a1701c6","flat":"9fbbe7cdedc42c8114c3bcf3bc09d9a15edf82d4033458c2d8fb2a1fad59f674","letteringWeights":"3fab39c41a6b8d21070c4205a2d81f6744a879c6df7ebdfc7edb600880ae030c"},"outro":{"positions":"9fa3209480a18a88e9e25ddde27cb37b91f10f419497fa3f76f29fc0e9e57750","normals":"1491264f836fcbc91d231fd11744c6dddcfe38468e50b62e2e954bac8a1701c6","signatureWeights":"b8f06297ccbe6836a3ad357c41dd21af579ed32d37763fcaa8b6cf887a51b14a"},"publication":{"positions":"a446079459f2c7daa4965a63a7399a7b432c1f1349b474548394ccf9965e6d25","normals":"1491264f836fcbc91d231fd11744c6dddcfe38468e50b62e2e954bac8a1701c6","flat":"27de6d91bdfe1ddd053e2529469f0b7686d60e6b7ac9a96c7c146dd11d8cb0f8"}};
const actual={galois:context.window.CourseOpeningGalois.sample(72000),outro:context.window.CourseOpeningOutro.create(72000),publication:context.window.CourseOpeningGalois.sampleNode(72000,9)};
for(const[name,properties]of Object.entries(expected))for(const[key,hash]of Object.entries(properties))assert.equal(crypto.createHash('sha256').update(Buffer.from(actual[name][key].buffer)).digest('hex'),hash,name+'.'+key+' retains the approved coordinates and masks');
console.log('Fixed sand lettering: approved Mac geometry and masks match without canvas text or OS fonts');
