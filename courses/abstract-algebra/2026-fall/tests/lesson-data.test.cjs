/* Generated section payloads must match the authored teaching material exactly. */
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const root=path.resolve(__dirname,'..'),context=vm.createContext({window:{}});
for(const file of ['lesson-groups/content.js','lesson-groups/chapter-two.js','lesson-groups/exercises.js','lesson-groups/textbook-references.js','lesson-1/notebook-content.js','lesson-1/exercises.js'])vm.runInContext(fs.readFileSync(path.join(root,file),'utf8'),context);
const w=context.window,json=x=>JSON.parse(JSON.stringify(x));let count=0;
function check(folder,id,expected){assert.deepEqual(JSON.parse(fs.readFileSync(path.join(root,folder,'sections',id+'.json'),'utf8')),json(expected),`Rebuild section ${id} with scripts/build-lesson-data.cjs`);count++;}
for(const [id,book] of Object.entries(w.GroupCourseContent))check('lesson-groups',id,{book,exercises:w.GroupCourseExercises[id],references:w.GroupTextbookReferences[id]});
for(const [id,notebook] of Object.entries(w.LessonNotebookContent))check('lesson-1',id,{notebook,exercises:w.TextbookExercises.banks[id]});
console.log(`PASS: ${count} section payloads match their authored sources.`);
