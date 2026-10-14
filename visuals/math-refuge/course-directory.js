import {CLASSROOM_PROGRAMS} from './classroom-catalog.js';
export const COURSE_CHAPTERS=[1,2,3,4];
export function sectionEntries(sections,chapter){return sections.filter(s=>s.id.startsWith(chapter+'.')).flatMap(s=>s.id==='2.6'?[{...s,key:'2.6-upper',title:['2.6 上 · 西罗三大定理','2.6 A · Sylow theorems'],program:'sylow-theorems'},{...s,key:'2.6-lower',title:['2.6 下 · 西罗定理的应用','2.6 B · Applications of Sylow theorems'],program:'algebra-sylow'}]:[{...s,key:s.id,title:[s.id+' · '+s.title[0],s.id+' · '+s.title[1]],url:'https://birationalclass.github.io/shengmeng/courses/abstract-algebra/2026-fall/?view=lesson&section='+s.id}]);}
export class CourseDirectory{
 constructor(sections=[]){this.sections=sections;this.course=null;this.chapter=null;this.page=0;}
 get level(){return this.chapter?'sections':this.course?'chapters':'courses';}
 get breadcrumbs(){return this.chapter?['课堂','代数学 I','第'+this.chapter+'章']:this.course?['课堂','代数学 I']:['课堂'];}
 enter(key){if(key==='algebra-i'){this.course=key;this.chapter=null;}else if(/^chapter:[1-4]$/.test(key)){this.course='algebra-i';this.chapter=Number(key.split(':')[1]);}else return false;this.page=0;return true;}
 back(){if(this.chapter)this.chapter=null;else this.course=null;this.page=0;}
 entries(language='zh'){const en=language==='en';if(!this.course)return[{key:'algebra-i',title:en?'Algebra I':'代数学 I',description:en?'Chapters 1–4':'第1—4章',branch:true}];if(!this.chapter)return COURSE_CHAPTERS.map(c=>({key:'chapter:'+c,title:en?'Chapter '+c:'第'+c+'章',description:this.sections.filter(s=>s.id.startsWith(c+'.')).map(s=>s.id).join(' · '),branch:true}));return sectionEntries(this.sections,this.chapter).map(s=>({...s,title:s.title[en?1:0],description:s.program?(en?'Blackboard classroom':'板书课堂'):(en?'Original courseware ↗':'原课程 ↗')}));}
 visible(language='zh',size=4){const all=this.entries(language),pages=Math.max(1,Math.ceil(all.length/size));this.page=Math.max(0,Math.min(this.page,pages-1));return{items:all.slice(this.page*size,(this.page+1)*size),page:this.page,pages};}
 locate(program){const p=CLASSROOM_PROGRAMS.find(p=>p.id===program);if(!p)return;this.course='algebra-i';this.chapter=2;const all=this.entries();this.page=Math.floor(Math.max(0,all.findIndex(x=>x.program===program))/4);}
}
