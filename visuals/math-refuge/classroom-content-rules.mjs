export const TEXTBOOK_SHA256='aee38591bb521ac7b6dce93fdb40de7221c8df74c05c72ba4dbac9087de22259';
const refs={
 2:['定义 2.6.1—2.6.2','Definitions 2.6.1–2.6.2',[125],'教材定义二点六点一和二点六点二分别规定 P 群与西罗 P 子群。'],
 3:['定理 2.6.1—2.6.2；推论 1','Theorems 2.6.1–2.6.2; Corollary 1',[125,126],'这里使用教材定理二点六点一、二点六点二，以及推论一。'],
 4:['推论 2','Corollary 2',[127],'这一板介绍教材推论二，也就是西罗子群的共轭性。'],
 6:['定理 2.6.3；推论 3','Theorem 2.6.3; Corollary 3',[127,128],'这里合用教材定理二点六点三与推论三。'],
 7:['定理 2.6.3 · 证明；推论 3','Theorem 2.6.3 · Proof; Corollary 3',[127,128],'我们解释教材定理二点六点三的证明和推论三。'],
 9:['定理 2.6.3 · 证明（2）','Theorem 2.6.3 · Proof (2)',[127],'这一板对应教材定理二点六点三证明中的第二部分。'],
 10:['习题 2-6 · 第 1 题','Exercise 2-6 · No. 1',[129],'这就是教材习题二杠六的第一题。'],
 19:['习题 2-6 · 第 8 题 · 第一步','Exercise 2-6 · No. 8 · Step 1',[129],'第二课时继续教材习题二杠六的第八题。'],
 20:['习题 2-6 · 第 8 题 · 第二步','Exercise 2-6 · No. 8 · Step 2',[129],'继续教材习题二杠六第八题的证明。'],
 21:['习题 2-6 · 第 8 题 · 第三步','Exercise 2-6 · No. 8 · Step 3',[129],'这一板完成教材习题二杠六第八题的证明。'],
 31:['习题 2-6 · 第 18 题','Exercise 2-6 · No. 18',[130],'现在介绍教材习题二杠六的第十八题。'],
 32:['例 1','Example 1',[128],'三十五阶群的题目是本节教材例一。']
};
// Each exercise remains intelligible when the preceding blackboard is hidden.
const contexts=[
 ['G 为有限群，|G|=72。','对 p=2、3 分别求 |G|=pᵃm 中的 pᵃ、m。'],
 ['G 为有限群，|G|=24；H≤G 且 |H|=4。','判断 H 是不是 2 子群、Sylow 2 子群。'],
 ['G=S₃，H=⟨(12)⟩，|H|=2。','判断包含 H 的 Sylow 2 子群是否唯一。'],
 ['G 有限，P、Q 是 G 的 Sylow p 子群。','辨别“同构”与“作为 G 的子集相等”。'],
 ['G=S₃，取三循环 a=(123)。','列出 ⟨a⟩，比较 ⟨(123)⟩ 与 ⟨(132)⟩。'],
 ['G 为有限群，|G|=24；nₚ 表示 Sylow p 子群个数。','同时使用整除与同余条件筛选 n₂、n₃。'],
 ['|G|=pᵃm，p∤m，P 是 Sylow p 子群。','证明 nₚ=[G:N_G(P)] 整除 m。'],
 ['G 是非交换群，取子群 P=G。','求 N_G(P)、C_G(P)，比较集合保持与逐点固定。'],
 ['G 有限；固定 Sylow p 子群 P，以共轭作用于全部 Sylow p 子群。','证明固定点只有 P，从而 nₚ≡1 (mod p)。'],
 ['G=S₃；其 Sylow 3 子群只有一个，Sylow 2 子群有三个。','利用唯一性判断这两类子群的正规性。'],
 ['G 为有限群，|G|=12；n₃∈{1,4}。','分别说明两个分支能推出什么、不能推出什么。'],
 ['G 为有限群，|G|=20；已有唯一的 5 阶正规子群。','检查“有正规 5 阶子群 ⇒ G 循环”是否成立。'],
 ['G=A₄；置换从右向左作用。','验证 (12)(34)=(132)(134)，检查三循环生成的元素。'],
 ['G=A₄，有八个三循环；每个 3 阶子群是循环群。','从非单位元的数量计算 Sylow 3 子群个数。'],
 ['|G|=24；Sylow 2 子群为 8 阶，个数记为 n₂。','判断 n₂(8−1) 是否能无重复地计数所有非单位 2 幂阶元素。'],
 ['分别设 |G|=18 与 |G|=45。','对两群找非平凡真正规子群，并求 45 阶群的 n₃。'],
 ['G=S₃，P=⟨(123)⟩ 是正规子群。','验证 (12)(123)(12)⁻¹=(132)，解释正规为何不等于逐元素交换。'],
 ['G 为有限群，|G|=15。','准备证明 G 循环：先求两个 Sylow 子群的阶、个数与正规性。'],
 ['G 为有限群，|G|=15；P、Q 分别为 Sylow 3、5 子群。','证明 P、Q 存在、唯一并且正规，注明每一步依据。'],
 ['|G|=15；P、Q 分别为 3、5 阶正规子群；x∈P，y∈Q。','证明交换子 xyx⁻¹y⁻¹∈P∩Q={e}，得到 xy=yx。'],
 ['P=⟨x⟩，|x|=3；Q=⟨y⟩，|y|=5。','直接求 P×Q 中 (x,y) 的阶，完成 15 阶群的循环性证明。'],
 ['分别考虑 |G|=15 与 |G|=21；nₚ 表示 Sylow p 子群个数。','比较 n₃ 的候选值，指出循环性论证为何开始分叉。'],
 ['在 F₇ 上令 Tᵢ,ⱼ(x)=2ʲx+i；i 模 7，j 模 3；乘法为复合。','计算两种复合顺序，验证此 21 阶群不交换。'],
 ['G={x↦2ʲx+i}，a(x)=x+1，b(x)=2x，均在 F₇ 上。','证明 ⟨a⟩ 正规，并求 G 的 Sylow 3 子群个数 n₃。'],
 ['G={x↦2ʲx+i}；H_c={x↦2ʲx+(1−2ʲ)c：j=0,1,2}。','列出 H₀、H₁，比较其非单位元素。'],
 ['G 为有限群，|G|=30；n₅、n₃ 表示两类 Sylow 子群个数。','证明 G 存在非平凡真正规子群。'],
 ['|G|=30；反设 n₅=6 且 n₃=10。','数出互不重复的单位元、5 阶元素、3 阶元素，导出矛盾。'],
 ['G 为有限群，|G|=30；已证 n₅=1 或 n₃=1。','说明至少一个 Sylow 子群非平凡、真包含且正规，核对证明依赖。'],
 ['|G|=12，n₃=4；反设 G 是单群，ρ 为四个 Sylow 3 子群上的共轭作用。','解释为何 ρ 非平凡且 Ker ρ={e}，不能只由“四个点”断言忠实。'],
 ['V={e,(12)(34),(13)(24),(14)(23)}≤A₄。','验证 V 为 4 阶真正规子群，以排除 12 阶单群。'],
 ['|G|=pq，p<q 为素数，p∤(q−1)。','证明 G 循环，并检验条件对 35 阶、21 阶的差别。'],
 ['G 为有限群，|G|=35。','写出 G 是循环群的完整证明，核对同态、单射、满射与生成元。'],
 ['G 为有限群，|G|=42；nₚ 是 Sylow p 子群个数。','检查由部分元素数的上界反推各 nₚ 取最大值的错误。'],
 ['G 有限，P 是 Sylow p 子群；另比较 S₃、21 阶仿射群。','辨别唯一性、正规性、交换性与循环性，给出理由或反例。'],
 ['分别考虑有限群的阶为 15、21、30、12。','复述各题的证明目标和关键步骤，不把四个目标混在一起。'],
 ['本课工具为西罗定理、拉格朗日定理、群作用与同态。','整理“完整条件—结论—反例提醒”，核对课后证明。']
];
export function applyClassroomRules(boards){
 if(boards.length!==contexts.length)throw Error('Review exercise contexts when the curriculum changes');
 for(const [i,b] of boards.entries()){
  b.originalIndex=i+1;b.clipPrefix='b'+String(i<18?i+1:i+3).padStart(2,'0');
  const ref=refs[i+1];b.reference=ref?{kind:'textbook',label:ref.slice(0,2),pdfPages:ref[2],sha256:TEXTBOOK_SHA256}:{kind:'extension',label:['扩展','Extension']};
  b.exercise={given:contexts[i][0],goal:contexts[i][1],prompt:b.activity,reference:{kind:'extension',label:['随堂练习','Classroom exercise']}};
  b.objective=[contexts[i][1],b.enTitle];
  const groups={18:['15 阶群结构','Groups of order 15','证明 G≅C₁₅','Prove G≅C₁₅.'],19:['15 阶群结构','Groups of order 15','证明 G≅C₁₅','Prove G≅C₁₅.'],20:['15 阶群结构','Groups of order 15','证明 G≅C₁₅','Prove G≅C₁₅.'],21:['15 阶群结构','Groups of order 15','证明 G≅C₁₅','Prove G≅C₁₅.'],22:['21 阶群结构','Groups of order 21','正规 7 阶子群存在；G 未必交换','A normal subgroup of order 7 exists; G need not be abelian.'],23:['21 阶群结构','Groups of order 21','构造一个非交换的 21 阶群','Construct a nonabelian group of order 21.'],24:['21 阶群结构','Groups of order 21','构造一个非交换的 21 阶群','Construct a nonabelian group of order 21.'],25:['21 阶群结构','Groups of order 21','求出仿射例子的七个 3 阶子群','Find the seven subgroups of order 3 in the affine example.'],26:['30 阶群结构','Groups of order 30','证明 G 有非平凡真正规子群','Prove G has a nontrivial proper normal subgroup.'],27:['30 阶群结构','Groups of order 30','证明 G 有非平凡真正规子群','Prove G has a nontrivial proper normal subgroup.'],28:['30 阶群结构','Groups of order 30','证明 G 有非平凡真正规子群','Prove G has a nontrivial proper normal subgroup.'],29:['12 阶群结构','Groups of order 12','证明 G 不是单群','Prove G is not simple.'],30:['12 阶群结构','Groups of order 12','证明 G 不是单群','Prove G is not simple.'],31:['pq 阶群结构','Groups of order pq','在 p<q、p∤(q−1) 的条件下证明 G 循环','Under p<q and p∤(q−1), prove G is cyclic.'],32:['35 阶群结构','Groups of order 35','证明 G≅C₃₅','Prove G≅C₃₅.']};
  if(i+1!==18&&groups[i+1]){const [zh,en,gzh,gen]=groups[i+1];b.topic=[zh,en];b.subtitle=[b.title.includes('：')?b.title.split('：').slice(1).join('：'):b.title,b.enTitle];b.objective=[gzh,gen];}
  if(i+1===19)b.subtitle=['西罗子群的正规性','Normality of the Sylow subgroups'];
  if(i+1===20)b.subtitle=['两个子群的交换性','Commutativity of the two subgroups'];
  if(i+1===21)b.subtitle=['建立直积同构','Constructing the direct-product isomorphism'];
  if(i+1===19)b.emphasis={3:{fragment:String.raw`n_5=1`,tone:'conclusion'},4:{fragment:String.raw`n_3=1`,tone:'conclusion'},5:{fragment:String.raw`P\trianglelefteq G,\ Q\trianglelefteq G`,tone:'conclusion'}};
  const cautions={3:[5],12:[4],13:[1],14:[5],15:[5],17:[1,3],33:[5]};
  if(cautions[i+1])b.emphasis=Object.fromEntries(cautions[i+1].map(row=>[row,{tone:'caution'}]));
  const conclusions={10:[5],20:[5],21:[5],28:[1,2],32:[5]};
  if(conclusions[i+1])b.emphasis=Object.fromEntries(conclusions[i+1].map(row=>[row,{tone:'conclusion'}]));
  if(ref)b.intro=ref[3]+b.intro;
 }
}

export const TEXTBOOK_PROBLEMS={
 1:{title:'习题2-6 第1题',enTitle:'Exercise 2-6 · No. 1',pdfPages:[129],lines:[['证明：有限群 G 有唯一的 Sylow p 子群 P 的充分必要条件','Prove: a finite group G has a unique Sylow p-subgroup P'],['是 P 是 G 的正规子群。','if and only if P is normal in G.']],speech:['原题要证明的是一个充分必要条件，群必须有限，P 是它的西罗 P 子群。','要证明唯一性与正规性等价，两个方向都不能遗漏。']},
 8:{title:'习题2-6 第8题',enTitle:'Exercise 2-6 · No. 8',pdfPages:[129],lines:[['证明：阶为15的群一定是循环群。','Prove: every group of order 15 is cyclic.']],speech:['原题要求证明：每一个十五阶群都是循环群。题目要求的是整个群的循环性，只找出正规子群还没有完成证明。']},
 18:{title:'习题2-6 第18题',enTitle:'Exercise 2-6 · No. 18',pdfPages:[130],lines:[['设 G 是 pq 阶群，其中 p、q 是素数，p<q 且 p∤q−1。','Let G have order pq, where p,q are primes, p<q and p∤(q−1).'],['证明：G 是循环群。','Prove: G is cyclic.']],speech:['原题设群的阶是两个素数 P 和丘的乘积。P 小于丘，而且 P 不整除丘减一，这两个条件都要保留。','题目要求证明这个群是循环群。下一板再展开西罗子群计数，检查这些条件分别用在哪里。']},
 example1:{title:'例1',enTitle:'Example 1',pdfPages:[128],lines:[['设有限群 G 的阶为35。证明：G 是循环群。','Let G be a finite group of order 35. Prove: G is cyclic.']],speech:['教材例一设有限群的阶为三十五，要求证明这个群是循环群。它是教材例题，不是另外编造的习题编号。']}
};
export function insertTextbookProblems(first,second){
 const problem=id=>{const q=TEXTBOOK_PROBLEMS[id],original=String(id);return {...q,statementOnly:true,clipPrefix:'q2-6-'+original,reference:{kind:'textbook',role:'problem',label:[q.title,q.enTitle],pdfPages:q.pdfPages,sha256:TEXTBOOK_SHA256},lines:q.lines.map(([text,enText],i)=>({text,enText,speech:q.speech[i]})),intro:'先读教材原题，明确全部条件和要求，再展开证明。',activity:'独立读题：写下原题已知条件和要证明的结论。',answer:q.lines.map(l=>l[0]).join(''),exercise:{original:[q.lines.map(l=>l[0]).join(''),q.lines.map(l=>l[1]).join(' ')],given:q.lines[0][0],goal:q.lines.at(-1)[0],prompt:'写下本题的条件与完整目标，不提前用证明步骤替代题目。',reference:{kind:'textbook',label:[q.title,q.enTitle]}}};};
 first.splice(first.findIndex(b=>b.originalIndex===10),0,problem(1));first.push(problem(8));
 second.splice(second.findIndex(b=>b.originalIndex===31),0,problem(18));second.splice(second.findIndex(b=>b.originalIndex===32),0,problem('example1'));
}
