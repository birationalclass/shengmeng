export const REPORT_STYLES=[
 {id:'exchange',label:'亲切交流',description:'谦虚、明亮，像与同行交流；少量思考停顿，不设课堂任务。'},
 {id:'research',label:'沉稳研究',description:'表达克制，假设与结论清楚，关键证明处放慢；不逐字念板书。'},
 {id:'story',label:'问题叙事',description:'从一个有依据的反差或困难展开；轻微幽默，不夸张，不调侃听众。'}
];
export const OPENING_ROUTES=[{id:'auto',label:'智能推荐'},{id:'example',label:'简单例子切入'},{id:'conjecture',label:'大问题 / 猜想切入'},{id:'problem',label:'核心问题切入'}];
export const DEFAULT_REPORT_SETTINGS={version:1,voiceGender:'male',voiceCharacter:'bright',rate:1,style:'exchange',titleSeconds:25,opening:'auto',audience:'mixed',goal:'balanced',talkMinutes:55,humor:'subtle',fillers:'light'};
const pick=(v,choices,fallback)=>choices.includes(v)?v:fallback;
const number=(v,lo,hi,fallback)=>Number.isFinite(Number(v))?Math.max(lo,Math.min(hi,Number(v))):fallback;
export function normalizeReportSettings(raw={}){
 if(!raw||typeof raw!=='object')raw={};const d=DEFAULT_REPORT_SETTINGS;
 return {...d,voiceGender:pick(raw.voiceGender,['male','female'],d.voiceGender),voiceCharacter:pick(raw.voiceCharacter,['bright','steady'],d.voiceCharacter),rate:number(raw.rate,.75,1.3,d.rate),style:pick(raw.style,REPORT_STYLES.map(s=>s.id),d.style),titleSeconds:Math.round(number(raw.titleSeconds,15,40,d.titleSeconds)),opening:pick(raw.opening,OPENING_ROUTES.map(r=>r.id),d.opening),audience:pick(raw.audience,['mixed','specialist'],d.audience),goal:pick(raw.goal,['balanced','proof','motivation'],d.goal),talkMinutes:Math.round(number(raw.talkMinutes,20,90,d.talkMinutes)),humor:pick(raw.humor,['none','subtle'],d.humor),fillers:pick(raw.fillers,['none','light'],d.fillers)};
}
export function reportFacts(report){
 return {hasExample:(report?.id==='ye'||report?.basedOn==='ye'),hasVerifiedConjecture:false,example:(report?.id==='ye'||report?.basedOn==='ye')?'一维 Hardy 不等式':null};
}
export function recommendReportOpening(settings,facts={}){
 const s=normalizeReportSettings(settings);let route=s.opening,reason='按你的切入方式编排。',warning='';
 if(route==='auto'){
  if(facts.hasVerifiedConjecture&&(s.audience==='specialist'||s.goal==='motivation')){route='conjecture';reason='同行背景较集中，且有已核验的大问题可作为共同起点。';}
  else if(facts.hasExample&&s.audience==='mixed'){route='example';reason='听众背景混合，先用一个可完整解释的简单例子建立共同对象。';}
  else{route='problem';reason='先说清研究对象与一个核心问题，再进入结果。';}
 }
 if(route==='conjecture'&&!facts.hasVerifiedConjecture){warning='尚无已核验猜想，不把研究目标写成著名猜想；建议改从核心问题进入。';}
 if(route==='example'&&!facts.hasExample)warning='需从原文核验合适例子，不能为了轻松而编造结论。';
 return {route,label:OPENING_ROUTES.find(r=>r.id===route).label,reason,warning};
}
export function buildReportPlan(raw,report={}){
 const s=normalizeReportSettings(raw),opening=recommendReportOpening(s,reportFacts(report)),style=REPORT_STYLES.find(v=>v.id===s.style);
 const titleScript=(report.id==='ye'||report.basedOn==='ye')?'大家好，很荣幸受到数学庇护所的邀请。我是叶东，这是我和黄侠合作的一项工作。今天报告的题目是：格点上的渐近最优 Hardy–Rellich 不等式。':'大家好，很荣幸有机会与各位交流。先介绍今天的题目与合作者。';
 return {version:1,report:{id:report.id||null,speaker:report.speaker||'',topic:report.topic||'',source:report.url||''},settings:s,recommendation:opening,titleBoard:{targetSeconds:s.titleSeconds,script:titleScript,allowed:['问候','必要合作说明','报告题目'],forbidden:['未定义记号','后续证明工具清单','主定理细节'],titleNarrationAfterWriting:true},firstContentBoard:{route:opening.route,example:opening.route==='example'?reportFacts(report).example:null},style:{...style,humor:s.humor,fillers:s.fillers},boardRules:{mainRows:[5,6],sideNotesExcluded:true,interleaveExplanation:true,lineSpeechCoverageRequired:true,oneAudioFilePerBoard:true},production:{requiresNewAudioAndBoardAudit:true,preserveActualTiming:true,doNotRelabelExistingRecording:true},outline:[`标题板 · ${s.titleSeconds} 秒目标`,`${opening.label} · 第二块起，逐步定义对象`,'主要结论 · 假设明确后再给出','证明主线 · 每块一个小目标','结束 · 贡献、限制与讨论'],notice:'风格、性别和切入方式用于制作新版本；现有录音不会因保存方案而变换内容。'};
}
export function reportPlanPrompt(plan){
 const s=plan.settings;return `使用 $math-refuge-report 为 ${plan.report.speaker} 的“${plan.report.topic}”制作报告。\n来源：${plan.report.source}\n音色目标：${s.voiceGender==='female'?'女声':'男声'}，${s.voiceCharacter==='bright'?'明亮交流':'沉稳自然'}；语速 ${s.rate.toFixed(2)}×；风格：${plan.style.label}。\n时长接近 ${s.talkMinutes} 分钟；标题板目标 ${s.titleSeconds} 秒，只含问候、必要合作说明和题目，题目写完才介绍，不预讲后续数学。\n正文采用${plan.recommendation.label}。${plan.recommendation.reason}${plan.recommendation.warning}\n主板含标题 5–6 行，解释和公式交错；每行必须有语义口播锚点，长公式概括含义即可。每块板书一个语音片段，按实测音频同步。换板只一句承接。\n语气谦虚、不好为人师；幽默${s.humor==='none'?'关闭':'少量温和'}；语气词${s.fillers==='none'?'关闭':'低频自然使用，思考的嗯可稍延长'}。\n保存方案不应冒充已经生成新音色或新报告。先核验来源和逐行同步，再发布。`;
}
export function mountReportSettings(document,{getLecture=()=>null,getReport=()=>getLecture()?.report,storage=globalThis.localStorage,onRate=()=>{},download=defaultDownload}={}){
 const root=document.getElementById('reportSettings');if(!root)return null;let settings;
 try{settings=normalizeReportSettings(JSON.parse(storage?.getItem('refuge-report-settings-v1')||'{}'));}catch{settings=normalizeReportSettings();}
 const controls=[...root.querySelectorAll('[data-report-setting]')],status=root.querySelector('[data-plan-status]');
 const read=()=>normalizeReportSettings(Object.fromEntries(controls.map(e=>[e.dataset.reportSetting,e.value])));
 const save=()=>{try{storage?.setItem('refuge-report-settings-v1',JSON.stringify(settings));}catch{}};
 function refresh(){const plan=buildReportPlan(settings,getReport());root.querySelector('[data-plan-recommendation]').textContent=plan.recommendation.label+' · '+plan.recommendation.reason+(plan.recommendation.warning?' '+plan.recommendation.warning:'');root.querySelector('[data-plan-title-script]').textContent=plan.titleBoard.script;root.querySelector('[data-title-seconds]').textContent=settings.titleSeconds+' 秒';root.querySelector('[data-report-rate]').textContent=settings.rate.toFixed(2)+' ×';root.querySelector('[data-plan-style]').textContent=plan.style.description;root.querySelector('[data-plan-voice]').textContent=settings.voiceGender==='female'?'女声制作目标已选；当前报告尚无完整女声，需生成女声版本后才能加载。':'完整男声可在上方音色列表加载；这里选择新报告的声音气质。';}
 for(const e of controls){e.value=String(settings[e.dataset.reportSetting]);e.addEventListener('input',()=>{settings=read();save();if(e.dataset.reportSetting==='rate')onRate(settings.rate);refresh();status.textContent=e.dataset.reportSetting==='rate'?'语速已应用，板书仍随实际语音同步。':'制作方案已保存；当前报告内容保持原版本。';});}
 root.querySelector('[data-plan-export]').addEventListener('click',()=>{const plan=buildReportPlan(settings,getReport());download(new Blob([JSON.stringify({...plan,prompt:reportPlanPrompt(plan)},null,2)],{type:'application/json'}),'难民营报告_'+(plan.report.id||'新报告')+'_制作方案.json');status.textContent='方案已下载，含 skill 指令、标题开场与板书规则。';});
 root.querySelector('[data-plan-smart]').addEventListener('click',()=>{const gender=settings.voiceGender;settings=normalizeReportSettings({...settings,style:'exchange',opening:'auto',titleSeconds:25,audience:'mixed',goal:'balanced',humor:'subtle',fillers:'light',voiceGender:gender});controls.forEach(e=>e.value=String(settings[e.dataset.reportSetting]));save();refresh();status.textContent='已采用适合混合背景听众的推荐方案；保留音色性别和语速。';});
 refresh();onRate(settings.rate);return {refresh,get settings(){return {...settings};},get plan(){return buildReportPlan(settings,getReport());}};
}
function defaultDownload(blob,name){const url=URL.createObjectURL(blob),a=document.createElement('a');a.href=url;a.download=name;a.click();setTimeout(()=>URL.revokeObjectURL(url),1000);}
