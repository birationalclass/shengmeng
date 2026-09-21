import cloudbase from '@cloudbase/node-sdk';
import {webcrypto} from 'node:crypto';
import {handle} from './service.mjs';
import {createStore} from './store.mjs';
import {handleHttp} from './http.mjs';
globalThis.crypto??=webcrypto;
const app=cloudbase.init({env:process.env.TCB_ENV||process.env.SCF_NAMESPACE});
const store=createStore(app.database(),process.env.RECORDS_COLLECTION_PREFIX||'sudoku_');
export async function main(event,context){
 // Read the current invocation's trusted context, never an event-supplied identity.
 const trusted=cloudbase.getCloudbaseContext(context);
 const env={store,secret:process.env.RECORDS_SECRET,password:process.env.RECORDS_ADMIN_PASSWORD,
  identity:trusted.TCB_UUID||trusted.WX_OPENID||trusted.TCB_SOURCE_IP,
  adminIdentity:trusted.TCB_SOURCE_IP||trusted.TCB_UUID||trusted.WX_OPENID};
 if(event.httpMethod){
  env.identity=trusted.TCB_SOURCE_IP||event.requestContext?.identity?.sourceIp||'gateway';
  env.adminIdentity=env.identity;env.origins=process.env.RECORDS_ORIGINS;
  // A lecture room may share a public IP. Keep an IP cap without locking out the class.
  env.lookupLimit=200;
  return handleHttp(event,env);
 }
 return handle(event,env);
}
