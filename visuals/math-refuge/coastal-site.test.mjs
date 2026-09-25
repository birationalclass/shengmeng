import {CAMPUS_ANCHOR,COAST_LIFT} from './elliptic-site.js';
import test from 'node:test';import assert from 'node:assert/strict';
import {findShore,shoreDistance,surfGain,OCEAN_ORIGIN,studyCoordinates} from './coastal-site.js';
import {seaDepthAt} from './sea-depth.js';import {BUILDING_SCALE as S} from './site-layout.js';
test('Ocean Study shoreline follows campus bathymetry rather than a second painted edge',()=>{for(let z=-15;z<=30;z+=3){const x=findShore(z);if(x!==null){assert(Math.abs(seaDepthAt(x,z))<1e-6);assert(seaDepthAt(x+.03,z)>0);assert(seaDepthAt(x-.03,z)<0);const ca=studyCoordinates(x*S,z*S);assert(Math.abs(88-ca[0]-x*S)<1e-8);}}assert.equal(findShore(-60),null);});
test('surf attenuates continuously with three-dimensional distance and remains bounded',()=>{const x=CAMPUS_ANCHOR,y=2.55+COAST_LIFT;assert(shoreDistance({x,y,z:0})<1e-5);assert(shoreDistance({x,y:y+40,z:0})>=40);let last=.321;for(let d=0;d<=2000;d+=.1){const gain=surfGain(d);assert(gain>=0&&gain<=.32);assert(gain<=last);assert(last-gain<.002);last=gain;}assert(surfGain(1000)<.001);});
