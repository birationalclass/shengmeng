import {RECORDS_CONFIG} from './records-config.mjs?v=records6-oneline';
import {createRecordsApi} from './records-api.mjs?v=records6-oneline';
// Loaded separately in <head>: warming the server never waits for the 3D bundle.
const initial=typeof window!=='undefined'&&navigator.onLine!==false
 ?createRecordsApi({config:RECORDS_CONFIG,t:zh=>zh})('/api/health').catch(()=>null):null;
let consumed=false;
export function takeWarmup(){if(consumed)return null;consumed=true;return initial;}
