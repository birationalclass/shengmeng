import {toBeach,beachDistance,COAST_LIFT} from './elliptic-site.js?v=true-north-coast-1';
import {seaDepthAt} from './sea-depth.js?v=true-north-coast-1';
import {BUILDING_SCALE as S} from './site-layout.js';
export const OCEAN_ORIGIN=[88,-.65*S,-35];
export function studyCoordinates(x,z){return [88-x,z+35];}
export function findShore(z){let left=54,right=84;if(seaDepthAt(left,z)>=0)return null;for(let i=0;i<28;i++){const mid=(left+right)/2;if(seaDepthAt(mid,z)>0)right=mid;else left=mid;}return (left+right)*.5;}
export function shoreDistance(position){const p=toBeach(position.x,position.z);return Math.hypot(Math.max(0,beachDistance(...p)-4),position.y-(2.55+COAST_LIFT));}
export function surfGain(distance){return .32/(1+(Math.max(0,distance)/24)**1.65);}
