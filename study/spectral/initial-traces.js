// One source-selection policy for the numbered initial definitions.
const definitions={1:{effect:'delta1',maxIndex:3},2:{effect:'delta2',maxIndex:3},4:{effect:'anticommute',maxIndex:3},6:{maxIndex:2}};
export function initialTraceContext(state){
 const definition=!state.cover&&state.module==='initial'&&state.step===0?definitions[state.initialReveal]:null;
 if(!definition)return null;
 return {...definition,effect:definition.effect||(state.totalStep===1?'totalsquare':'totalmap'),origin:state.totalOrigin||{p:1,q:1}};
}
export function selectableTraceOrigin(state,p,q){
 const context=initialTraceContext(state);
 return !!context&&[p,q].every(i=>Number.isInteger(i)&&i>=0&&i<=context.maxIndex);
}
