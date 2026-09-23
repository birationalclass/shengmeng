import test from 'node:test';
import assert from 'node:assert/strict';
import {terracePaving} from './terrace-paving.js';
import {HALL,SEA_TERRACE} from './site-layout.js';

test('terrace shares continuous joints around all four sides of the hall',()=>{
  const [w,e,n,s]=SEA_TERRACE,bounds=[w+.18,e-.18,n+.18,s-.18];
  const {cells,xs,zs}=terracePaving(bounds,HALL);
  for(const x of [HALL.west,HALL.east])assert(xs.some(v=>Math.abs(v-x)<1e-8));
  for(const z of [HALL.north,HALL.south])assert(zs.some(v=>Math.abs(v-z)<1e-8));
  let area=0;
  for(const {bounds:[a,b,c,d]} of cells){
    assert(b-a>.2&&d-c>.2,'No thin tile slivers at the border');
    assert(a>=bounds[0]&&b<=bounds[1]&&c>=bounds[2]&&d<=bounds[3]);
    assert(b<=HALL.west+1e-8||a>=HALL.east-1e-8||d<=HALL.north+1e-8||c>=HALL.south-1e-8,'No paving beneath the hall');
    assert.equal(xs.indexOf(b)-xs.indexOf(a),1);
    assert.equal(zs.indexOf(d)-zs.indexOf(c),1);
    area+=(b-a)*(d-c);
  }
  const expected=(bounds[1]-bounds[0])*(bounds[3]-bounds[2])-(HALL.east-HALL.west)*(HALL.south-HALL.north);
  assert(Math.abs(area-expected)<1e-7,'Paving covers the exterior without missing strips');
  assert.equal(new Set(cells.map(c=>c.bounds.join(','))).size,cells.length);
});
