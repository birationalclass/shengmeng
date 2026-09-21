// Precompute public puzzle clues: avoid expensive puzzle generation on a free Worker.
import {createRequire} from 'node:module';
import {writeFileSync} from 'node:fs';
const model=createRequire(import.meta.url)('../../../courses/abstract-algebra/2026-fall/lesson-1/associativity-sudoku.js');
const clues=Object.fromEntries(Array.from({length:8},(_,i)=>[i+2,model.initial(i+2)]));
writeFileSync(new URL('./clues.mjs',import.meta.url),'// Generated from the public game model. No student data.\nexport default '+JSON.stringify(clues)+';\n');
