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
console.log('PASS: all scenes show English then Chinese, complete the configured fade, and retain English during Gandalf dialogue');
