import test from 'node:test';
import assert from 'node:assert/strict';
import {equationLines} from './chalk-layout.mjs';
test('preserve leading coefficient brackets after a displayed line break',()=>{
 const tex=String.raw`\begin{gathered}A=B\\[1-\alpha(1+o_d(1))]E_\gamma\ge C\\[2pt]D=F\end{gathered}`;
 assert.deepEqual(equationLines(tex),['A=B',String.raw`[1-\alpha(1+o_d(1))]E_\gamma\ge C`,'D=F']);
});
test('nested cases and bracketed matrices are not row spacing',()=>{
 const tex=String.raw`\begin{gathered}[a,b]\\\begin{cases}x,&a\\y,&b\end{cases}\\[-.5em]z\end{gathered}`;
 assert.deepEqual(equationLines(tex),['[a,b]',String.raw`\begin{cases}x,&a\\y,&b\end{cases}`,'z']);
});
