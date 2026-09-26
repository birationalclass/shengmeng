// Public CC0 surface photographs only; reference-video frames are not assets.
import fs from 'node:fs/promises';
import {createHash} from 'node:crypto';
const directory=new URL('./assets/',import.meta.url),manifest=[];
for(const [id,prefix] of [['pine_bark','bark'],['forest_ground_06','forest'],['rock_boulder_dry','cliff']]){
  const response=await fetch(`https://api.polyhaven.com/files/${id}`);
  if(!response.ok)throw new Error(`Asset metadata: ${id} ${response.status}`);
  const files=await response.json();
  for(const [channel,suffix] of [['Diffuse','color'],['nor_gl','normal']]){
    const url=files[channel]['1k'].jpg.url,result=await fetch(url);
    if(!result.ok)throw new Error(`Asset download: ${result.status} ${url}`);
    const bytes=Buffer.from(await result.arrayBuffer()),file=`${prefix}-${suffix}.jpg`;
    await fs.writeFile(new URL(file,directory),bytes);
    manifest.push({file,asset:id,channel,resolution:'1k',bytes:bytes.length,sha256:createHash('sha256').update(bytes).digest('hex'),source:`https://polyhaven.com/a/${id}`,license:'CC0-1.0',licenseURL:'https://polyhaven.com/license',downloadURL:url});
    console.log(file,bytes.length);
  }
}
await fs.writeFile(new URL('landscape-sources.json',directory),JSON.stringify(manifest,null,2)+'\n');
