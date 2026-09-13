const assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),vm=require('node:vm');
const window={};for(const file of ['opening-backdrop.js','opening-narration.js'])vm.runInNewContext(fs.readFileSync(path.join(__dirname,'..',file),'utf8'),{window});
const classes=new Set(),element={dataset:{},classList:{add:n=>classes.add(n),remove:n=>classes.delete(n)}};
const scenes=window.CourseOpeningBackdrop.scenes,n=window.CourseOpeningNarration.create(element,scenes);
for(let i=0;i<scenes.length;i++){
 n.setScene(i,0);assert.equal(element.lang,'en');assert.ok(element.textContent.length>0);const original=element.textContent;
 n.tick(7900,true);assert.equal(element.textContent,original);assert.equal(classes.has('is-language-changing'),false);
 n.tick(100,true);assert.equal(classes.has('is-language-changing'),true);
 n.tick(2399,true);assert.equal(element.textContent,original,'do not replace text during fade-out');
 n.tick(1,true);assert.equal(element.lang,'zh-CN');assert.ok(element.textContent.length>0);assert.equal(classes.has('is-language-changing'),false);
 n.tick(20000,true);assert.equal(element.lang,'zh-CN','Chinese remains for the rest of this scene');
}
n.setScene(5,1);const verse=element.textContent;assert.equal(verse.split('\n').length,4);
n.tick(18000,true,{holdEnglish:true});assert.equal(element.textContent,verse);assert.equal(classes.has('is-language-changing'),false,'English stays throughout original dialogue');
n.tick(1,true);n.tick(2400,true);assert.equal(element.lang,'zh-CN');assert.equal(element.textContent.split('\n').length,4);
n.setScene(5,2);assert.equal(element.lang,'zh-CN');assert.equal(classes.has('is-language-changing'),true,'a new single-figure cycle fades back to English');
n.tick(2400,true);assert.equal(element.lang,'en');
n.tick(8000,false);assert.equal(classes.has('is-language-changing'),false,'hidden narration does not consume reading time');
n.tick(8000,true);n.tick(900,true,{fadeMs:900});assert.equal(element.lang,'zh-CN','the setting controls the language fade duration');
n.reset();n.setScene(5,2);assert.equal(element.lang,'en','replay starts with English again');
const chineseScenes=[
 {language:'zh',kind:'history',en:'A young mathematician',zh:'少年走进数学。'},
 {language:'zh',verse:{en:'A letter to the future',zh:'将已有研究写进致朋友的信。'}},
 scenes[0]
];
const chinese=window.CourseOpeningNarration.create(element,chineseScenes);
for(let i=0;i<2;i++){
 chinese.setScene(i,0);assert.equal(element.lang,'zh-CN','Chinese-only scenes start without an English frame');assert.equal(chinese.language,'zh');
 const text=element.textContent;assert.equal(text,chineseScenes[i].verse?.zh||chineseScenes[i].zh);assert.equal(chinese.needsFrames,false);
 chinese.tick(60000,true,{holdEnglish:true,englishMs:0,fadeMs:0});assert.equal(element.textContent,text,'the voice hold cannot override a Chinese-only scene');assert.equal(classes.has('is-language-changing'),false);
 for(const cycle of [1,-1,2]){chinese.setScene(i,cycle);chinese.tick(80000,true);assert.equal(element.lang,'zh-CN');assert.equal(element.textContent,text);assert.equal(classes.has('is-language-changing'),false,'cycles do not fade Chinese-only narration back to English');}
 chinese.reset();chinese.setScene(i,0);assert.equal(element.lang,'zh-CN','replay retains the scene language');assert.equal(element.textContent,text);
}
chinese.setScene(2,0);assert.equal(element.lang,'en','ordinary scenes keep the bilingual sequence');chinese.tick(8000,true);chinese.tick(2400,true);assert.equal(element.lang,'zh-CN');
console.log('PASS: ordinary scenes retain English/Chinese fading and voice holds; Chinese-only narration stays Chinese on entry, cycles, voice holds and replay');
