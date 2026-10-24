let converters;
export async function convertScript(text,script='traditional'){
 if(script==='original')return text;
 if(!['simplified','traditional'].includes(script))throw Error('请选择简体、繁体或保留原文。');
 if(!converters)converters=import('./vendor/opencc/full.js').then(mod=>{const api=mod.default||mod;return {traditional:api.Converter({from:'cn',to:'tw'}),simplified:api.Converter({from:'tw',to:'cn'})};}).catch(error=>{converters=null;throw error;});
 return (await converters)[script](text);
}
