import assert from 'node:assert/strict';
import fs from 'node:fs';
import vm from 'node:vm';
import * as C from './cube-core.mjs';
import {verifyCertificate,STATE_BOUND} from './certificate.mjs';
import {LESSONS} from './lessons.mjs';
let checks=0;const check=(condition,message)=>{assert.ok(condition,message);checks++;};
// Independent 48-label face cycles from Harvard Mathematics' GAP example.
const harvardFaces=['U','L','F','R','B','D'];
const cycles=[[[1,3,8,6],[2,5,7,4],[9,33,25,17],[10,34,26,18],[11,35,27,19]],[[9,11,16,14],[10,13,15,12],[1,17,41,40],[4,20,44,37],[6,22,46,35]],[[17,19,24,22],[18,21,23,20],[6,25,43,16],[7,28,42,13],[8,30,41,11]],[[25,27,32,30],[26,29,31,28],[3,38,43,19],[5,36,45,21],[8,33,48,24]],[[33,35,40,38],[34,37,39,36],[3,9,46,32],[2,12,47,29],[1,14,48,27]],[[41,43,48,46],[42,45,47,44],[14,22,30,38],[15,23,31,39],[16,24,32,40]]];
const labels=harvardFaces.flatMap(f=>C.FACELETS.map((s,i)=>({s,i})).filter(({s})=>s.face===f&&!(s.row===1&&s.col===1)).map(({i})=>i));
for(let k=0;k<6;k++){const p=C.identity();for(const c of cycles[k])c.forEach((n,i)=>p[labels[n-1]]=labels[c[(i+1)%c.length]-1]);check(C.equal(p,C.MOVES[harvardFaces[k]]),`Independent ${harvardFaces[k]} cycle check`);}
for(const f of C.FACES){check(C.equal(C.power(C.MOVES[f],4),C.identity()),`${f}⁴=e`);check(C.order(C.MOVES[f])===4n,`${f} has order exactly 4`);check(C.equal(C.compose(C.MOVES[f],C.inverse(C.MOVES[f])),C.identity()),`${f} inverse`);}
const alg=s=>C.algorithmPermutation(C.parseAlgorithm(s));
check(!C.equal(alg('R U'),alg('U R')),'Noncommutativity witness');
check(C.order(alg('R U'))===105n,'RU order');check(C.order(alg('[R,U]'))===6n,'Commutator order');
check(C.equal(alg('(R U R\' U\')6'),C.identity()),'Six commutators restore');
check(C.equal(alg('[F:[R,U]]'),alg("F R U R' U' F'")),'Nested conjugate parser');
check(C.equal(alg('R2′ U′'),alg("R2 U'")),'Prime normalization');
for(const bad of ['X','R3','(R','[R,U','[R]','(R)99999','R;alert(1)','[R,]']){assert.throws(()=>C.parseAlgorithm(bad));checks++;}
let seed=0x14567;const random=()=>{seed=(1664525*seed+1013904223)>>>0;return seed/2**32;};
let p=C.identity();for(let i=0;i<2000;i++){
  const f=C.FACES[Math.floor(random()*6)],q=C.power(C.MOVES[f],[1,2,3][Math.floor(random()*3)]);p=C.compose(p,q);
  const s=C.invariants(p);check(s.legal,'All three invariants along seeded walk');check(C.equal(C.fromCubies(s),p),'Cubie ↔ facelet reconstruction');
  const before=C.cubies(p),g=C.cubies(q),after=C.cubies(C.compose(p,q));
  check(after.co.every((v,k)=>v===(before.co[g.cp[k]]+g.co[k])%3),'Corner orientation composition');
  check(after.eo.every((v,k)=>v===(before.eo[g.ep[k]]+g.eo[k])%2),'Edge orientation composition');
}
for(const kind of ['flip','twist','parity']){const s=C.impossible(kind);check(!C.invariants(s).legal,`${kind} impossible`);for(const f of C.FACES)check(!C.invariants(C.compose(s,C.MOVES[f])).legal,`${kind} obstruction persists under ${f}`);}
const certificate=JSON.parse(fs.readFileSync(new URL('./certificate.json',import.meta.url)));const result=verifyCertificate(certificate);check(result.lowerBound===43252003274489856000n&&STATE_BOUND===result.lowerBound,'Certified state count');
const corrupt=structuredClone(certificate);corrupt.nodes.at(-1)[1]=[];assert.throws(()=>verifyCertificate(corrupt));checks++;
const wrongOrbit=structuredClone(certificate);wrongOrbit.levels[0].orbitSize=23;assert.throws(()=>verifyCertificate(wrongOrbit));checks++;
const wrongFixer=structuredClone(certificate);wrongFixer.levels.at(-1).generators=[0,1,2,3,4,5];assert.throws(()=>verifyCertificate(wrongFixer));checks++;
const ctx={module:{exports:{}},exports:{},console};vm.runInNewContext(fs.readFileSync(new URL('../../../study/spectral/vendor/katex.min.js',import.meta.url),'utf8'),ctx);
let formulas=0;for(const lesson of LESSONS)for(const [,encoded] of lesson.body.matchAll(/data-tex="([^"]+)"/g)){const tex=encoded.replaceAll('&quot;','"').replaceAll('&lt;','<').replaceAll('&amp;','&');assert.doesNotThrow(()=>ctx.module.exports.renderToString(tex,{throwOnError:true,strict:'ignore'}),`${lesson.id}: ${tex}`);formulas++;}
console.log(`PASS: ${checks} checks; ${formulas} formulas; six independently specified face turns; exact orbit certificate.`);
