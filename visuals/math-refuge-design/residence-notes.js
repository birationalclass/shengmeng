import {PAPERS} from './residence-profile.js?v73-residence';
const HOME='../../';
const pages={
 '海上住宅':{title:'孟晟 · 海上住宅',text:'住宅岛位于园区以西，离现有建筑群边缘约 1 公里。庭院将研究、会客和生活空间分开；左侧可选择房间。',links:[['建筑平面与剖面','./residence-plan.html?v76-villa'],['个人主页',HOME]]},
 '住宅玄关':{title:'学术足迹',text:'Sheng Meng · 孟晟\n华东师范大学数学科学学院\n\n2022—至今 · 华东师范大学\n2019—2022 · 韩国高等科学研究院\n2018—2019 · 马克斯·普朗克数学研究所\n2013—2018 · 新加坡国立大学博士，导师张德齐',links:[['CV','https://math.ecnu.edu.cn/~smeng/CV.pdf']]},
 '住宅书房':{title:'研究与论文',text:'代数几何 · 双有理几何 · 动力系统\n书架旁的目录收录主页当前的 25 项论文与预印本。',papers:true,links:[['主页研究目录',HOME+'#research']]},
 '住宅展廊':{title:'数学可视化收藏',text:'把抽象结构转化为可以观察、旋转和探索的对象。室内雕塑是空间引子；下列链接进入实际交互作品。',links:[['三维可视化',HOME+'visuals/real3d/'],['Julia 集',HOME+'visuals/julia/'],['混沌吸引子',HOME+'visuals/chaos/'],['向量丛与直纹曲面',HOME+'visuals/vector-bundle/'],['Pascal 线',HOME+'visuals/pascal/'],['谱序列',HOME+'study/spectral/']]},
 '住宅工作室':{title:'AI · 数学 · 游戏',text:'AI4Math：形式推理、猜想发现、数学知识系统。\n\nmsreader 将 TeX 和 arXiv 论文组织为定理卡片、证明链接与知识图谱。\n\nAI4Games 探索策略、规则与智能体。',links:[['AI4Math',HOME+'#ai4math'],['msreader',HOME+'msreader.html'],['无尽',HOME+'endless/'],['疆域争锋',HOME+'game/'],['DLSGraph',HOME+'#tools']]},
 '住宅客厅':{title:'交流与联系',text:'欢迎数学研究、学生咨询，以及数学、人工智能与游戏领域的交流。\n\n华东师范大学\n统计楼 115 室\n上海市东川路 500 号，200241',links:[['smeng@math.ecnu.edu.cn','mailto:smeng@math.ecnu.edu.cn'],['ORCID','https://orcid.org/0000-0003-4500-7241'],['个人主页',HOME]]},
 '住宅套房':{title:'留给生活的空间',text:'主卧、衣帽收纳与独立盥洗区。木格栅过滤海边的光线，与研究和会客空间保持距离。',links:[]},
 '住宅露台':{title:'海景与留白',text:'天之道，损有余而补不足。\n\n茶席、浅水庭院与面向海面的休息区。',links:[['Study',HOME+'study/'],['抽象代数课程',HOME+'courses/abstract-algebra/2026-fall/?view=course']]}
};
export function createResidenceNotes(){
 const button=document.createElement('button');button.id='residenceNotesButton';button.className='chrome';button.textContent='住宅札记';button.hidden=true;button.setAttribute('aria-expanded','false');
 const panel=document.createElement('aside');panel.id='residenceNotes';panel.className='chrome';panel.hidden=true;panel.setAttribute('aria-label','住宅区域与主页信息');
 document.body.append(button,panel);let current='';
 const link=(name,url)=>{const a=document.createElement('a');a.textContent=name+' ↗';a.href=url;a.target='_blank';a.rel='noopener noreferrer';return a;};
 button.addEventListener('click',()=>{panel.hidden=!panel.hidden;button.setAttribute('aria-expanded',String(!panel.hidden));});
 return {update(name){const data=pages[name];button.hidden=!data;if(!data){panel.hidden=true;button.setAttribute('aria-expanded','false');current='';return;}if(name===current)return;current=name;panel.replaceChildren();const close=document.createElement('button');close.className='residence-close';close.textContent='×';close.setAttribute('aria-label','关闭住宅札记');close.onclick=()=>{panel.hidden=true;button.setAttribute('aria-expanded','false');};const label=document.createElement('p');label.className='residence-kicker';label.textContent='SHENG MENG / RESIDENCE';const h=document.createElement('h2');h.textContent=data.title;const p=document.createElement('p');p.textContent=data.text;panel.append(close,label,h,p);if(data.papers){const list=document.createElement('ol');for(const paper of PAPERS){const item=document.createElement('li');const title=document.createElement('h3');title.textContent=paper.title;const authors=document.createElement('p');authors.textContent=paper.authors;const venue=document.createElement('p');venue.textContent=paper.year+' · '+paper.venue;item.append(title,authors,venue,link('Link',paper.url));list.append(item);}panel.append(list);}const links=document.createElement('nav');links.setAttribute('aria-label','相关主页链接');for(const [text,url] of data.links)links.append(link(text,url));panel.append(links);button.textContent=data.title+' · 札记';},dispose(){button.remove();panel.remove();}};
}
