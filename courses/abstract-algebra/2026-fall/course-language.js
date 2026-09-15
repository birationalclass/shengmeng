/* Local, deterministic translations; nothing is sent to a translation service. */
(()=>{
  const key='shengmeng-course-language-v1',dictionary=new Map(),originals=new WeakMap(),attributes=new WeakMap();
  let language='zh',scheduled=false,observer;
  try{language=new URLSearchParams(location.search).get('lang')||localStorage.getItem(key)||'zh';}catch{}
  if(language!=='en')language='zh';
  function translate(text){const trimmed=text.trim();if(dictionary.has(trimmed))return text.replace(trimmed,dictionary.get(trimmed));
    const replacements=[
      [/《近世代数》第三版/g,'Modern Algebra, 3rd edition'],[/等价关系与集合的分类/g,'Equivalence relations and partitions'],[/群的概念/g,'The concept of a group'],[/方幂与指数法则/g,'Integer powers and exponent laws'],[/群的例子 · 几何演示/g,'Group examples · geometry'],[/概念检查/g,'Concept check'],[/教材/g,'Textbook'],[/定义/g,'Definition'],[/定理/g,'Theorem'],[/习题/g,'Exercises'],[/例 (?=\d)/g,'Example '],[/课后练习：/g,'Exercises: '],[/第 ([\d—]+) 页/g,'pp. $1'],[/结论：/g,'Conclusion: '],[/；右消去同理/g,'; right cancellation is analogous'],
      [/第 (\d+) 周 · 周一至周日/g,'Week $1 · Mon–Sun'],[/第 (\d+) 周 · 周([一四六])/g,(_,n,d)=>`Week ${n} · ${{一:'Mon',四:'Thu',六:'Sat'}[d]}`],[/第 ([\d—]+) 节/g,'Periods $1'],[/第 ([\d—]+) 周/g,'Weeks $1'],[/([\d]+) 学时/g,'$1 hours'],[/([\d]+) 项安排 · 全学期/g,'$1 schedule entries · semester total'],[/下一次课 ·/g,'Next class ·'],
      [/([abc]) 与自身无关系/g,'$1 is not related to itself'],[/ 缺少反向/g,' has no reverse arrow'],[/ 缺少捷径/g,' has no direct arrow'],[/补入 (\d+) 个有序对，得到包含原关系的最小等价关系。/g,'Added $1 ordered pairs to obtain the smallest equivalence relation containing the original.'],
      [/商集 S \/ ∼ 有 (\d+) 个元素，每个元素都是 S 的一个子集。/g,'The quotient S / ∼ has $1 elements, each a subset of S.'],[/同一类可以有不同的名字：(.+) 与 (.+) 是同一个集合。/g,'A class may have different names: $1 and $2 are the same set.'],[/整数有无穷多个，模 (\d+) 的等价类恰好有/g,'There are infinitely many integers, but the number of classes modulo $1 is exactly'],[/^(\d+) 个$/g,'$1'],[/。商集 (.+) 的元素是这些类。/g,'. These classes are the elements of $1.'],
      [/，与 k、ℓ 的取值无关。/g,', independent of k and ℓ.'],[/这次计算与标准代表的结果相差 (.+)。/g,'The difference from the standard representatives is $1.'],[/全部 (\d+) 个三元组均满足/g,'All $1 triples satisfy associativity'],[/双侧单位元是 /g,'The two-sided identity is '],[/ 不在集合内/g,' is outside the set'],[/ 无逆元/g,' have no inverse'],[/(.+) 与 (.+) 互为双侧逆元。/g,'$1 and $2 are two-sided inverses.'],[/只满足当前方向的等式。/g,'Only this direction holds.'],[/反例：/g,'Counterexample: '],[/（先右后左）/g,' (right to left)'],[/ 的运算表/g,' operation table'],
      [/计算 /g,'Calculate '],[/从单位元开始，运算 0 次/g,'start at the identity; apply the operation zero times'],[/每次加 /g,'add each time: '],[/每次乘 /g,'multiply each time by '],[/（a 的逆元）/g,' (the inverse of a)'],[/加法记号下：(.+)，负倍数通过负元 (.+) 计算。/g,'In additive notation: $1; negative multiples use the additive inverse $2.'],[/零次幂等于单位元 (.+)；(.+) 的逆元是 (.+)，所以负指数表示重复乘这个逆元。/g,'The zeroth power is the identity $1. The inverse of $2 is $3; negative powers repeatedly multiply this inverse.'],
      [/有向关系图：同色节点属于同一等价类/g,'Directed relation graph: equal colors indicate one equivalence class'],[/有向关系图：当前关系不满足全部等价关系性质/g,'Directed relation graph: not all equivalence properties hold'],[/([abc]) 与 ([abc]) (有|没有)关系，点击切换/g,(_,a,b,v)=>`${a} ${v==='有'?'is':'is not'} related to ${b}; toggle`],[/选择代表元 (.+)，属于 (.+) 类/g,'Choose representative $1 in class $2'],[/模 (.+) 的分类。代表元 (.+) 属于剩余类 (.+)；商集共有 (.+) 个元素。/g,'Classes modulo $1. Representative $2 belongs to $3; the quotient has $4 elements.']
    ];
    for(const [pattern,replacement] of replacements)text=text.replace(pattern,replacement);
    text=text.replace(/(\d+) 次课/g,'$1 classes').replace(/(\d+) 项安排/g,'$1 schedule entries').replace(/具体时段待定/g,'times to be announced');
    return text;
  }
  function apply(){scheduled=false;document.documentElement.lang=language==='en'?'en':'zh-CN';
    const root=document.body;if(!root)return;
    observer?.disconnect();
    const walker=document.createTreeWalker(root,NodeFilter.SHOW_TEXT,{acceptNode(node){const p=node.parentElement;return p&&!p.closest('script,style')&&(!p.closest('#symmetry-particle-studies')||p.closest('#openingLoader'))?NodeFilter.FILTER_ACCEPT:NodeFilter.FILTER_REJECT;}});
    let changed=false;
    let node;while(node=walker.nextNode()){
      const saved=originals.get(node);let source=node.data;
      if(saved&&(node.data===saved.zh||node.data===saved.en))source=saved.zh;
      const translated=translate(source);originals.set(node,{zh:source,en:translated});const next=language==='en'?translated:source;if(node.data!==next){node.data=next;changed=true;}
    }
    root.querySelectorAll('[aria-label],[placeholder],[title],[data-label]').forEach(el=>{
      if(el.closest('#symmetry-particle-studies'))return;
      let saved=attributes.get(el);if(!saved){saved={};attributes.set(el,saved);}
      ['aria-label','placeholder','title','data-label'].forEach(key=>{const current=el.getAttribute(key);if(current===null)return;const old=saved[key],source=old&&(current===old.zh||current===old.en)?old.zh:current,en=translate(source),next=language==='en'?en:source;saved[key]={zh:source,en};if(current!==next)el.setAttribute(key,next);});
    });
    observe();if(changed)window.LessonScreen?.refresh();
  }
  function queue(){if(!scheduled){scheduled=true;requestAnimationFrame(apply);}}
  function observe(){if(observer&&document.body)observer.observe(document.body,{childList:true,subtree:true,characterData:true});}
  window.CourseLanguage={get language(){return language;},translate,add(entries){Object.entries(entries).forEach(([zh,en])=>dictionary.set(zh,en));queue();},set(value){const next=value==='en'?'en':'zh';if(next===language){queue();return;}language=next;try{localStorage.setItem(key,language);}catch{}apply();window.dispatchEvent(new Event('course-language'));}};
  window.addEventListener('storage',event=>{if(event.key===key)window.CourseLanguage.set(event.newValue);});
  function init(){observer=new MutationObserver(records=>{if(records.some(r=>!r.target.parentElement?.closest('svg,#relation-graph,#quotient-graph,#symmetry-graph,#symmetry-second')))queue();});observe();queue();}
  if(document.readyState==='loading')document.addEventListener('DOMContentLoaded',init,{once:true});else init();
})();

