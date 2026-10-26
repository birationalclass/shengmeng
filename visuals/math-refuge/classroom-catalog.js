const COURSE_PACK_INDEX={"sylow-theorems":"./assets/course-packs/v1/sylow-theorems-f9200f21bceb80f056df.json","algebra-sylow":"./assets/course-packs/v1/algebra-sylow-5db11f9c16b759eb3ac1.json","rings-basics":"./assets/course-packs/v1/rings-basics-908503424dfa20da71ca.json","rings-ideals":"./assets/course-packs/v1/rings-ideals-3856caa6a026f1661bac.json","rings-homomorphisms":"./assets/course-packs/v1/rings-homomorphisms-6fa7bdc2792b28c63cda.json","rings-prime-maximal":"./assets/course-packs/v1/rings-prime-maximal-25caacaeccaad417779d.json","rings-characteristic":"./assets/course-packs/v1/rings-characteristic-a386163dcf086e5f14b0.json"};
const COURSE_URL='https://birationalclass.github.io/shengmeng/courses/abstract-algebra/2026-fall/';
const VOICE_LABEL='ZL · C明亮开课';
function program({id,label,labelEn,chapter,section,sections=[section],sectionPart='',topic,topicEn,courseManifest,pagesManifest,narrationManifest,audioRoot,rosterLocalOnly=false}){
 return {id,resourceIndex:globalThis.REFUGE_LOCAL?undefined:COURSE_PACK_INDEX[id],kind:'classroom',speaker:'子皿曰成',speakerEn:'Zimin Yuecheng',assistant:'孟晟',assistantEn:'Sheng Meng',label,labelEn,courseId:'algebra-i',chapter,section,sections,sectionPart,topic,topicEn,
  courseManifest,audioRoot,rosterLocalOnly,manifest:pagesManifest,
  narration:{manifest:narrationManifest,language:'zh',synthetic:true,defaultPlaybackRate:1,label:VOICE_LABEL,voices:[{id:'zl',label:VOICE_LABEL,manifest:narrationManifest}]},
  url:'./sylow-f-classroom.html?course='+id,sourceLabel:'课件、逐行讲稿与课堂任务',courseURL:COURSE_URL+'?view=lesson&section='+sections[0]};
}
function sylowProgram(id,label,labelEn){
 const upper=id==='sylow-theorems',suffix=upper?'-pronunciation-de-v1':'-stabilizer-v5',version='?v=neutral-de-20261026',audioRoot='./assets/audio/courses/zl-c-20261019/'+id+'/';
 return program({id,label,labelEn,chapter:2,section:'2.6',sectionPart:upper?'上':'下',topic:upper?'§2.6 上 · 西罗三大定理':'§2.6 下 · 西罗定理的应用',topicEn:upper?'§2.6 A · Sylow theorems':'§2.6 B · Applications of Sylow theorems',
  courseManifest:'./assets/chalk/zl-c-20261019/'+id+suffix+'.json'+version,pagesManifest:'./assets/chalk/zl-c-20261019/'+id+suffix+'-pages.json'+version,narrationManifest:audioRoot+'narration'+suffix+'.json'+version,audioRoot});
}
function ringsProgram(id,label,labelEn,sections){
 const section=sections.join('—'),version='?v=zl-name-20261024',chalk='./assets/chalk/rings-20261022/'+id,audioRoot='./assets/audio/courses/rings-20261022/'+id+'/';
 return program({id,label,labelEn,chapter:3,section,sections,rosterLocalOnly:true,topic:'§'+section+' · '+label,topicEn:'§'+section+' · '+labelEn,courseManifest:chalk+'.json'+version,pagesManifest:chalk+'-pages.json'+version,narrationManifest:audioRoot+'narration.json'+version,audioRoot});
}
export const CLASSROOM_PROGRAMS=[
 sylowProgram('sylow-theorems','西罗三大定理','Sylow theorems'),
 sylowProgram('algebra-sylow','西罗定理的应用','Applications of Sylow theorems'),
 ringsProgram('rings-basics','环、整环与域','Rings, integral domains and fields',['3.1','3.2']),
 ringsProgram('rings-ideals','理想与商环','Ideals and quotient rings',['3.3']),
 ringsProgram('rings-homomorphisms','环的同态','Ring homomorphisms',['3.4']),
 ringsProgram('rings-prime-maximal','素理想与极大理想','Prime and maximal ideals',['3.5']),
 ringsProgram('rings-characteristic','环的特征与素域','Characteristic and prime fields',['3.6'])
];
export const classroomProgram=id=>CLASSROOM_PROGRAMS.find(program=>program.id===id);
