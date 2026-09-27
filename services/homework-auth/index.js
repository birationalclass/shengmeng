const cloudbase=require('@cloudbase/node-sdk');
const nodemailer=require('nodemailer');
const {createHandler}=require('./service.cjs');
const {createStore}=require('./store.cjs');
const {createWorkspace}=require('./workspace.cjs');
const {createAI}=require('./ai.cjs');
const {loadKey,saveKey}=require('./secrets.cjs');
const app=cloudbase.init({env:process.env.TCB_ENV||process.env.SCF_NAMESPACE});
const mailUser=process.env.SMTP_USER||'smeng@math.ecnu.edu.cn';
const transport=nodemailer.createTransport({host:process.env.SMTP_HOST||'smtphz.qiye.163.com',port:Number(process.env.SMTP_PORT||994),secure:true,
 auth:{user:mailUser,pass:process.env.SMTP_PASSWORD},connectionTimeout:8000,greetingTimeout:8000,socketTimeout:12000,logger:false,debug:false});
const store=createStore(app.database(),process.env.AUTH_COLLECTION_PREFIX||'homework_');
const options={
 secret:process.env.AUTH_SECRET,origins:(process.env.AUTH_ORIGINS||'https://birationalclass.github.io').split(','),
 mailReady:Boolean(process.env.SMTP_PASSWORD),teacherAccount:'smeng',teacherEmail:mailUser,
 async sendMail({to,code,purpose}){
  const info=await transport.sendMail({from:{name:'阅见 · 作业系统',address:mailUser},to,
   subject:`阅见 · ${purpose==='register'?'注册':'重设密码'}验证码`,
   text:`您的验证码是：${code}\n\n10 分钟内有效，仅能使用一次。\n请在作业系统中完成${purpose==='register'?'注册并设置个人密码':'密码重设'}。\n如非本人操作，请忽略此邮件。`});
  if(!info.accepted?.some(address=>address.toLowerCase()===to.toLowerCase()))throw Error('delivery refused');
 }
};
exports.main=async(event,context)=>{
 const trusted=cloudbase.getCloudbaseContext(context);
 const key=await loadKey(store,process.env.AUTH_SECRET);
 const handle=createHandler(store,{...options,workspace:createWorkspace(store,createAI({apiKey:key})),configureAI:apiKey=>saveKey(store,process.env.AUTH_SECRET,apiKey)});
 return handle({...event,trustedIp:trusted.TCB_SOURCE_IP||event.requestContext?.identity?.sourceIp||'gateway'});
};
