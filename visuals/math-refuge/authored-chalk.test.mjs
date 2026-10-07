import test from 'node:test';import assert from 'node:assert/strict';import {clipPolyline,clipRect,authoredContext} from './authored-chalk.js';
test('cropped SVG strokes remain inside the viewport without connecting separate pen contacts',()=>{const parts=clipPolyline([[-10,5],[5,5],[20,5],[20,20],[5,8]], [0,0,10,10]);assert.equal(parts.length,2);for(const part of parts)for(const [x,y] of part){assert(x>=0&&x<=10&&y>=0&&y<=10);}assert.deepEqual(parts[0],[[0,5],[5,5],[10,5]]);assert.deepEqual(clipPolyline([[-5,-5],[-1,-1]],[0,0,10,10]),[]);assert.deepEqual(clipRect([-100,2,200,4],[0,0,10,10]),[0,2,10,4]);});

test('recorded glyph operations retain their semantic narration row',()=>{
 const previous=globalThis.document;globalThis.document={};
 try{
  const ctx={font:'40px serif',fillStyle:'#fff',fillText(){},measureText(){return{width:20,actualBoundingBoxAscent:30,actualBoundingBoxDescent:8,actualBoundingBoxLeft:0,actualBoundingBoxRight:20};}};
  const recorder=authoredContext(ctx);recorder.ctx.fillText('汉字',20,50);
  const source=Object.assign([18,18,46,44],{mainLine:3,prose:'explanation'});
  const rows=recorder.rows([source]);assert.equal(rows.length,2);assert(rows.every(r=>r.mainLine===3&&r.prose==='explanation'));
 }finally{globalThis.document=previous;}
});
