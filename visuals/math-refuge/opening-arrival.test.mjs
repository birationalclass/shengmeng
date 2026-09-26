import assert from 'node:assert/strict';
import {openingArrival} from './opening-arrival.js';
import {HALL,SEAT_ROWS,BUILDING_SCALE as S,DECK_Y} from './site-layout.js';
const west=HALL.west*S-30,end=[SEAT_ROWS[1].x*S-30-.65,(DECK_Y+.028)*S+.18+1.65,0],p=openingArrival([-1400,450,0],west,0,end);
assert.deepEqual(p.sample(0),[-1400,450,0]);assert.deepEqual(p.sample(p.duration),end);
for(const t of [5.5,9.5]){const h=.0001,a=p.sample(t-h),b=p.sample(t),c=p.sample(t+h);for(let i=0;i<3;i++)assert.ok(Math.abs((b[i]-a[i])/h-(c[i]-b[i])/h)<.01);}
let old=p.sample(0);for(let t=.01;t<=p.duration;t+=.01){const q=p.sample(t);assert.ok(q[0]>=old[0]-.000001);if(q[0]>west-3){assert.ok(Math.abs(q[2])<1e-8);assert.ok(q[1]<3);}old=q;}
console.log('PASS: relocated door centerline, continuous velocity at approach/door joins, monotonic forward entry and second-row stop');
