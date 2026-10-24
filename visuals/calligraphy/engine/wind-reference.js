import {windReference as v10} from './wind-reference-v10.js';
export {windReferencePreset,windReferencePresetV8} from './wind-reference-v10.js';

// BV1PP4y1Z7Zv, 7.347–7.612 s: the outside of stroke 2 travels around
// the foot and returns UP the inner edge to the waist. Previously the
// two rails stopped at the bottom right, so the growing front never returned.
// Locally fitted rails, not the artist's recovered controls.
const px=([x,y,z])=>[(x-574)/120,(355-y)/120,z];
const strokes=v10.strokes.map(s=>({...s}));
const headA=v10.strokes[1].a.slice(0,17),headB=v10.strokes[1].b.slice(0,17);
const shortReturn=[
 [603,410,-.06],[613,461,-.07],[646,514,.10],[688,552,.24],[732,578,.32],[762,577,.27],
 [766,568,.25],[766,554,.25],[757,542,.29],[742,530,.34],
 [720,514,.42],[690,490,.48],[659,460,.50],[632,427,.51],
 [612,397,.51],[595,376,.50],[579,360,.48],[567,350,.44],[557,347,.40]
];
const longReturn=[
 [624,409,-.01],[674,446,-.14],[720,479,-.22],[766,501,-.20],
 [786,529,-.02],[782,544,.12],
 [771,548,.13],[770,540,.22],[765,531,.32],[753,517,.38],
 [735,500,.46],[706,478,.50],[674,449,.55],[646,415,.55],
 [626,384,.55],[608,365,.55],[591,351,.52],[575,343,.48],[557,347,.40]
];
Object.assign(strokes[1],{
 name:'横折弯钩 · 铺面回卷上挑',
 a:[...headA,...shortReturn.map(px)],b:[...headB,...longReturn.map(px)],
 terminalSectionFrom:30,interpolateBoundaries:true,
 front:[.18,.17,.10,.065,.07,.14,.25,.30,.22,.15,.18,.22,.22],
 back:[.12,.11,.065,.04,.045,.09,.16,.20,.14,.10,.12,.14,.14],
 camber:[0,-.04,-.07,-.02,0,-.10,-.17,-.08,-.01,0,.01,0,0],
 end:1.02,
 gesture:{anchor:'a',wake:.055,pressure:[.55,.9,1,.6,.5,.65,.95,.85,.7],
  roll:[-.1,.12,.05,-.12,.10,.18,-.25,-.12,.06],
  timing:[[0,0],[.12,.09],[.28,.27],[.43,.43],[.56,.58],[.69,.72],[.80,.84],[.90,.94],[1,1]],
  phases:[[0,'逆入蓄势'],[.16,'转锋折肩'],[.38,'提锋下行'],[.57,'按笔铺开钩面'],[.75,'沿内缘回卷'],[.90,'上挑移锋']]}
});
Object.assign(strokes[2],{
 name:'第三笔 · 承钩势落锋',start:1.14,
 connection:{from:'wind-main',type:'lifted-return',start:1.02,end:1.14},
 gesture:{...strokes[2].gesture,
  phases:[[0,'承二笔上挑落锋'],[.07,'按笔成肩'],[.28,'转锋长撇'],[.86,'提收入内']]}
});

export const windReference={...v10,strokes,
 referenceV9Strokes:v10.strokes,referenceV10Strokes:v10.strokes,
 revision:'wind-second-to-third-v11-20261024',
 method:'Stroke 2 has a broad scooped foot and a loaded return along its inner rim to the waist; a timed lifted transfer leads into stroke 3. The completed strokes have an open image gap. Existing inner-to-insect geometry is retained separately.',
 calibration:{...v10.calibration,returnFrames:[7.346791,7.474803,7.557132,7.611915],
  scope:'Manually fitted rail reparameterization and lifted transfer from visible frames. No source mesh or animation keys were obtained.'}
};
