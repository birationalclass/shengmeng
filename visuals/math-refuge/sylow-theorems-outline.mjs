import {TEXTBOOK_SHA256} from './classroom-content-rules.mjs';
const t=(text,enText,speech)=>({text,enText,speech}),f=(tex,speech)=>({tex,speech});
const ref=(label,en,pages)=>({kind:'textbook',label:[label,en],pdfPages:pages,sha256:TEXTBOOK_SHA256});
let number=0;
function b(title,enTitle,seconds,reference,lines,intro,given,goal,answer,emphasis={}){const i=++number;return{title,enTitle,plannedSeconds:seconds,originalIndex:i,clipPrefix:'th'+String(i).padStart(2,'0'),reference,lines,intro,activity:goal,answer,exercise:{given,goal,prompt:goal,reference:{kind:'extension',label:['随堂练习','Classroom exercise']}},emphasis};}
const first=ref('定理2.6.1 · 证明','Theorem 2.6.1 · Proof',[125,126]),second=ref('定理2.6.2 · 证明','Theorem 2.6.2 · Proof',[126,127]),third=ref('定理2.6.3 · 证明','Theorem 2.6.3 · Proof',[127,128]);
export const firstLesson=[
b('p 子群与西罗 p 子群','p-subgroups and Sylow p-subgroups',570,ref('定义2.6.1—2.6.2','Definitions 2.6.1–2.6.2',[125]),[
f(String.raw`|G|=p^a m,\quad p\nmid m,\quad a\ge1`,'设 G 为有限群，P 为整除群阶的素数。把所有的 P 因子取出来，群阶就写成 P 的 a 次方乘以艾姆，剩下的艾姆不再被 P 整除。这里 a 的含义是群阶中 P 的最高指数。'),
t('定义2.6.1：p 群的阶为 pᵏ，k≥1','Definition 2.6.1: a p-group has order pᵏ, k≥1.','教材定义二点六点一把阶为素数的正整数次幂的有限群称为 P 群。G 的一个子群自身是 P 群，就叫 P 子群。按照这本教材的约定，单位群不包括在这里。'),
f(String.raw`H\le G,\quad |H|=p^r,\quad1\le r\le a`,'因此一个 P 子群 H 的阶是 P 的 r 次方。拉格朗日定理给出子群阶整除群阶，所以 r 不会超过 a。这个整除条件是必要条件，还没有证明所有允许的阶数都有子群。'),
t('定义2.6.2：西罗 p 子群达到最高 p 幂','Definition 2.6.2: Sylow subgroups attain the maximal p-power.','教材定义二点六点二规定，若 P 的阶是 P 的 r 次方，而更高一阶的 P 幂不整除群阶，就称它为西罗 P 子群。在当前分解中，这恰好要求阶达到 P 的 a 次方。'),
f(String.raw`P\le G,\quad |P|=p^a\quad\text{(Sylow }p\text{-subgroup)}`,'定义说明什么样的子群合格，但定义本身并不保证这个对象存在。拉格朗日定理也不能直接反过来使用。接下来的第一西罗定理解决存在性，而且会同时给出所有较小的素数幂阶子群。')],
'今天从有限群的阶开始，讨论哪些素数幂阶子群一定存在。','G 为24阶有限群，H≤G，|H|=4。','判断 H 是不是2子群、是不是西罗2子群；说明两者的区别。','四是二的平方，所以 H 是二子群。二十四等于二的三次方乘以三，西罗二子群的阶须为八，因此 H 不是西罗二子群。'),
b('定理2.6.1 — 群阶的强归纳','Theorem 2.6.1 — induction',420,first,[
t("设 |G|=N，固定素数 p 及 1≤k≤a。","Let |G|=N; fix a prime p and 1≤k≤a.","现在考虑一个阶为 N 的有限群 G。把群阶写成 P 的 a 次方乘以与 P 互素的艾姆，并固定一到 a 之间的整数 k。当前要证的是：这个 G 中存在 P 的 k 次方阶子群。"),
t("归纳假设：定理对所有阶小于 N 的有限群 K 均成立。","Induction hypothesis: the theorem holds for every finite K with |K|<N.","归纳假设是：对于每一个阶严格小于 N 的有限群 K，第一西罗定理的完整陈述都成立。这包括任意整除 K 的阶的素数，以及对应范围内的每个指数。这里对群阶作强归纳，不是对指数 a 作归纳。"),
t("N=1 时无须证明；N=p 时直接取 G。","N=1 is vacuous; for N=p, use G itself.","从 N 等于一开始，此时没有素数整除群阶，结论无需证明。若当前 N 等于素数 P，只需取整个群 G。一般情况下，我们利用类方程寻找阶严格小于 N、又保留所需素数幂的群。"),
f(String.raw`|G|=|Z(G)|+\sum_i[G:C_G(x_i)]`,'艾克斯下标 i 遍历非中心共轭类的代表。每个共轭类的大小是群到相应中心化子的指数。为了把归纳用到更小的群，中心分支会转到商群，非中心分支会转到真中心化子。'),
t('分支：p∣|Z(G)|，或 p∤|Z(G)|','Split according to whether p divides |Z(G)|.','这两个分支穷尽所有情形。第一种情形利用中心里的素数阶元素，第二种情形利用类方程中的一项。两个分支最终都要构造出阶恰好为 P 的 k 次方的子群。')],
'定理已经完整陈述。下面对有限群的阶作强归纳，先把归纳假设与当前待证情形写清楚。','|G|=pᵃm，p∤m，1≤k≤a；对|G|归纳。','说明归纳参数是什么，两个分支分别准备转到哪类较小群。','归纳参数是群的阶。中心阶被 P 整除时转到商群；否则转到一个非中心元素的真中心化子。不是对 k 直接归纳。',{1:{fragments:['|G|=N']},2:{fragments:['N']}}),
b('第一定理 — 中心分支的商群','First theorem — a central quotient',420,first,[
t('设 p∣|Z(G)|，由已学结论取 p 阶元素','Assume p divides |Z(G)|; choose an element of order p.','中心是有限交换群。教材第二点二节例十二已经给出所需的素数阶元素结论，所以可以在中心中取 P 阶元素 z。这一步使用的是前面学过的结果，不能引用尚未证明的西罗定理。'),
f(String.raw`z\in Z(G),\quad |z|=p,\quad H=\langle z\rangle`,'由 z 生成的循环子群 H 有 P 个元素。H 包含在中心里，每个群元素都保持它的每个元素不变，因此 H 是正规子群。这样才能形成后面的商群。'),
f(String.raw`H\trianglelefteq G,\qquad |H|=p`,'这里的正规性来自中心，而不是来自子群阶是素数。一般的素数阶子群并不自动正规；本步的特殊条件正是 H 位于中心。'),
t('k=1 时 H 已满足要求；k≥2 时取商群','For k=1 use H; for k≥2 pass to the quotient.','若 k 等于一，H 本身就完成构造。这个边界情形单独处理，避免把单位群误叫 P 群。若 k 至少为二，商群的阶仍然有足够大的 P 幂，可以应用归纳。'),
f(String.raw`|G/H|=p^{a-1}m<|G|`,'商群的阶等于群阶除以 H 的阶，因此最高 P 指数恰好减少一。它的阶严格小于 G，而 k 减一介于一和 a 减一之间，所以归纳假设给出商群中 P 的 k 减一次方阶子群。')],
'先处理中心的阶被 P 整除的情形。','p∣|Z(G)|，z∈Z(G)，|z|=p，H=⟨z⟩。','证明 H 正规，并解释为什么 k=1 要单独处理。','H 包含于中心，所以任意共轭保持 H。k 等于一时 H 就是所求子群，不需要在商群里寻找非平凡 P 子群。',{3:{tone:'conclusion'},4:{tone:'caution'}}),
b('第一定理 — 把商群子群提升回来','First theorem — lifting a subgroup',300,first,[
t('k≥2；由归纳得到商群子群 Q','For k≥2, induction gives a subgroup Q in G/H.','现在 k 至少为二。归纳只给出商群中的子群 Q，还不是原群中的子群；要完成存在性证明，必须把它提升回来，并核对阶数。'),
f(String.raw`Q\le G/H,\qquad |Q|=p^{k-1}`,'Q 的每个元素是一个 H 的陪集。自然投影把 G 的元素送到对应陪集，因此可以把投影落在 Q 里的全部元素组成一个集合。'),
f(String.raw`\pi:G\to G/H,\qquad P=\pi^{-1}(Q)`,'同态的子群原像仍然是子群，所以 P 确实是 G 的子群。P 还包含 H，并且限制投影从 P 到 Q 是满射，核就是 H。'),
t('P≤G，H≤P，且 P/H≅Q','P≤G, H≤P, and P/H≅Q.','这里使用商群与子群的对应定理。不能把商群的元素当作 G 的元素随意挑代表来形成子群；取完整原像保证封闭性，也保证核保持不变。'),
f(String.raw`|P|=|H||Q|=p\cdot p^{k-1}=p^k`,'每个落在 Q 中的陪集有 P 个元素，而 Q 中有 P 的 k 减一次方个陪集。因此原像的阶正好是 P 的 k 次方，中心分支的构造完成。')],
'商群里找到子群后，原像把它带回原群。','H正规且|H|=p；Q≤G/H且|Q|=pᵏ⁻¹。','对 π 的原像 P 证明子群性，并计算它的阶。','子群的同态原像是子群。投影从 P 到 Q 的核是 H，故 P 的阶等于 H 的阶乘以 Q 的阶，也就是 P 的 k 次方。',{5:{tone:'conclusion'}}),
b('第一定理 — 非中心分支','First theorem — the noncentral case',600,first,[
t('设 p∤|Z(G)|，而 p∣|G|','Assume p does not divide |Z(G)|, but divides |G|.','这一分支无法从中心中取出 P 阶元素。类方程提供另一条路线：左侧被 P 整除，而中心项不被 P 整除，所以其他项不可能全部被 P 整除。'),
f(String.raw`\exists i:\ p\nmid[G:C_G(x_i)]`,'因此有一个非中心共轭类，其大小不被 P 整除。这个条件意味着从 G 的阶分解中除去该指数时，所有 P 因子都会保留在中心化子的阶里面。'),
f(String.raw`|G|=[G:C_G(x_i)]\,|C_G(x_i)|`,'指数乘法公式把这个直觉写成等式。由于前一个因子与 P 互素，后一个因子的最高 P 幂与 G 完全相同，而不仅仅是还能被 P 整除一次。'),
t('xᵢ 非中心，所以 C_G(xᵢ) 是真子群','Since xᵢ is noncentral, its centralizer is proper.','艾克斯下标 i 不是中心元素，因此总有群元素不与它交换，中心化子不等于 G。它的阶严格变小，正好满足归纳参数的要求。'),
f(String.raw`p^a\mid|C_G(x_i)|\Longrightarrow\exists P\le C_G(x_i):|P|=p^k`,'中心化子是阶更小的有限群，并保留 P 的 a 次方作为阶的因子。归纳给出其中 P 的 k 次方阶子群。子群包含关系可以继续到 G，所以它也是原群的子群。')],
'类方程会找到一个保留全部 P 因子的真中心化子。','p∤|Z(G)|，|G|=pᵃm；xᵢ取非中心共轭类代表。','解释“有一项不被p整除”和“中心化子保留pᵃ”两个推理，并说明何处用归纳。','若所有非中心类大小都被 P 整除，类方程模 P 的右侧就等于非零的中心项，矛盾。选中不被 P 整除的指数后，最高 P 幂留在中心化子里；它是阶更小的真子群，因此能用归纳。',{5:{tone:'conclusion'}}),
b('推论1 — 西罗子群的存在性','Corollary 1 — existence of Sylow subgroups',360,ref('推论1','Corollary 1',[126]),[
t('两个分支都得到 pᵏ 阶子群','Both branches produce a subgroup of order pᵏ.','中心分支通过商群归纳再取原像，非中心分支通过真中心化子归纳。构造方式不同，得到的阶数相同，因此固定 k 的存在性已经证明。'),
f(String.raw`1\le k\le a\Longrightarrow\exists H\le G:\ |H|=p^k`,'因为 k 是从一到 a 之间任意选的，每个允许的素数幂阶都出现。这个范围包含最大指数 a，也包含比 a 小的各个指数。'),
t('取 k=a，得到教材推论1','Take k=a to obtain Corollary 1.','把 k 取为 a，第一定理就给出阶为 P 的 a 次方的子群。它满足西罗 P 子群的定义，所以这个集合中至少有一个对象。'),
f(String.raw`\exists P\le G:\ |P|=p^a`,'这就是西罗子群存在性。现在可以固定一个西罗子群继续研究，但还没有证明任意的 P 子群被它的某个共轭包含，这将由第二定理解决。'),
t('存在性不推出唯一性，也不自动推出正规性','Existence alone gives neither uniqueness nor normality.','同一个阶数可能对应多个子群。第一定理只解决是否存在，不解决它们相互之间的关系。之后的共轭性和计数结论，才会把这些对象联系起来。')],
'第一定理已经完成，取最大指数得到存在性推论。','|G|=72=2³·3²。','列出第一定理保证的2幂阶、3幂阶子群，并说明尚不能判断什么。','第一定理保证二、四、八阶子群以及三、九阶子群存在。西罗二子群为八阶，西罗三子群为九阶；唯一性和正规性还没有从第一定理得到。',{4:{tone:'conclusion'},5:{tone:'caution'}})
];
export const secondLesson=[
b('引理1 — p 群作用的不动元素','Lemma 1 — a fixed point for a p-group action',570,ref('引理1','Lemma 1',[126]),[
t('设 p 群 H 作用于有限集合 X','Let a p-group H act on a finite set X.','引理把 P 群的阶数性质转成轨道性质。这里 H 是作用群，X 只是有限集合，不要求它有群结构。我们关心是否有被 H 的每个元素同时固定的点。'),
f(String.raw`|H\cdot x|=[H:H_x]=p^{r_x}`,'轨道稳定子定理说明，每个轨道的大小整除 H 的阶，因此都是 P 的幂。指数可以为零，此时轨道只有一个点；这个点被整个 H 固定。'),
t('非单点轨道的大小被 p 整除','Every nonsingleton orbit has size divisible by p.','若轨道不是单点，其大小至少是 P，于是一定被 P 整除。这一观察允许我们把全部轨道大小相加，再对 P 取模。'),
f(String.raw`|X|\equiv|X^H|\pmod p`,'X 上标 H 表示被 H 的所有元素固定的点的集合。非单点轨道在模 P 求和时消失，剩下的正是单点轨道，也就是不动点。'),
f(String.raw`p\nmid|X|\Longrightarrow X^H\ne\varnothing`,'若集合的大小不被 P 整除，不动点数就不能为零。这证明教材引理一。它并不保证不动点唯一；第二定理只需要存在一个不动陪集。')],
'第二定理的证明从这个不动元素引理开始。','H为p群，作用于有限集合X，p∤|X|。','证明 X 有不动点，并说明结论为何不是“不动点唯一”。','所有非单点轨道都被 P 整除。集合的总大小不被 P 整除，所以必须有单点轨道。这样的轨道可能不止一个，引理只保证至少一个。',{5:{tone:'conclusion'}}),
b('定理2.6.2 — 左陪集上的作用','Theorem 2.6.2 — an action on left cosets',360,second,[
t('H 为 p 子群，P 为任一西罗 p 子群','H is a p-subgroup and P is any Sylow p-subgroup.','第一定理已保证西罗子群存在。现在固定任意一个 P，并给定一个 P 子群 H。目标是找到群元素 g，使 H 落在 P 的这个共轭子群中。'),
f(String.raw`\exists g\in G:\ H\le gPg^{-1}`,'第二定理保留了这个量词顺序：先给 H 和任意的西罗子群 P，再寻找适合它们的 g。不是说 H 包含于 P 本身，也不是说所有 g 都能实现包含。'),
t('令 X 为 P 的全部左陪集组成的集合','Let X be the set of all left cosets of P.','这里不要求 P 正规。左陪集组成一个集合，足够让 H 作用；没有必要，也不能在未证明正规时把它当作商群使用。'),
f(String.raw`X=G/P,\qquad |X|=[G:P]=m`,'集合的大小是陪集个数。P 的阶达到最高 P 幂，所以指数是剩下的互素因子艾姆，恰好不被 P 整除。引理一现在有了可用的大小条件。'),
f(String.raw`h\cdot(gP)=hgP\qquad(h\in H)`,'用左乘定义 H 在 X 上的作用。若两个代表给出同一陪集，左乘 h 后仍然给出同一陪集，所以作用良定义。单位元和乘法相容性也都来自 G 的乘法。')],
'用 H 的左乘作用，把子群包含关系转成不动陪集。','H为G的p子群，P为任一西罗p子群。','核对左乘作用良定义，并说明为什么 X 的大小与p互素。','相同左陪集左乘同一个 h 后仍相同，因此作用不依赖代表。P 的阶是群阶中的最高 P 幂，所以左陪集个数等于互素因子艾姆。',{2:{tone:'conclusion'},3:{tone:'caution'}}),
b('第二定理 — 从不动陪集得到包含','Second theorem — fixed cosets give containment',360,second,[
t('由引理1，存在不动陪集 gP','Lemma 1 supplies a fixed coset gP.','H 是 P 群，陪集集合的大小是与 P 互素的艾姆，因此引理一保证一个不动点。不动点在这里是整个陪集 gP，而不是 G 的某个元素。'),
f(String.raw`hgP=gP\qquad\forall h\in H`,'这个陪集被 H 中每一个元素固定。这是全称条件，接下来对任意 h 作同样的变形，才能得到整个子群的包含关系。'),
f(String.raw`g^{-1}hg\in P\qquad\forall h\in H`,'两个左陪集相等的判据，把固定条件改写为 g 的逆、h、g 这个乘积属于 P。这个等价使用的是陪集判据，不需要 P 正规。'),
t('于是 H 的每个元素都属于 gPg⁻¹','Thus every element of H belongs to gPg⁻¹.','把包含的元素写成共轭形式，就得到 h 属于 g P g 的逆。由于 h 遍历 H，得到的是整个 H 的包含，而不是一个元素偶然落入。'),
f(String.raw`H\le gPg^{-1}`,'第二西罗定理证明完成。任意给定的 P 子群都包含在一个西罗子群中，而且可以把这个西罗子群选为任意固定 P 的某个共轭。')],
'不动陪集已经找到，剩下的是把条件准确翻译回子群。','对所有h∈H都有hgP=gP。','推出 H≤gPg⁻¹，并说明为什么不能只验证某个h。','固定条件对每个 h 成立，因此每个 h 都属于相应共轭子群，得到 H 的整体包含。只验证某个元素不能推出整个子群包含。',{5:{tone:'conclusion'}}),
b('推论2 — 西罗子群的共轭性','Corollary 2 — conjugacy',240,ref('推论2','Corollary 2',[127]),[
t('取 H、P 为两个西罗 p 子群','Take two Sylow p-subgroups H and P.','第二定理适用于所有 P 子群，因此也适用于另一个西罗子群 H。不同之处是这时 H 和 P 的阶相同，都达到最高 P 幂。'),
f(String.raw`H\le gPg^{-1}`,'先由第二定理得到包含。共轭不会改变子群的阶，所以右边的阶仍等于 P 的阶。'),
f(String.raw`|H|=|gPg^{-1}|=p^a`,'包含的两边是同样大小的有限集合，因此包含必须成为相等。这一步既用了有限性，也用了两个子群都是西罗子群。'),
f(String.raw`H=gPg^{-1}`,'这就是教材推论二：任意两个西罗 P 子群互相共轭。它说明这些子群在 G 内的相对位置可以通过内共轭联系。'),
t('互相共轭不表示作为子集相等','Conjugate subgroups need not be equal as subsets.','抽象同构、在 G 内共轭和作为子集相等，是不同强度的关系。共轭性本身不意味着西罗子群只有一个，下一步需要研究它们的个数。')],
'同阶使第二定理的包含加强为相等。','H、P均为G的西罗p子群，且H≤gPg⁻¹。','说明如何由包含得到共轭，以及为何不能由此断言唯一。','两边的阶相等，所以包含成为相等。这个相等把 H 写成 P 的一个共轭，并没有说所有共轭都等于 P 本身，因此还不能断言唯一。',{4:{tone:'conclusion'},5:{tone:'caution'}}),
b('定理2.6.3与推论3 — 计数结论','Theorem 2.6.3 and Corollary 3 — counts',180,ref('定理2.6.3；推论3','Theorem 2.6.3; Corollary 3',[127,128]),[
t('记 Sylₚ(G) 为全部西罗 p 子群的集合','Let Sylₚ(G) denote the set of Sylow p-subgroups.','P 子群和西罗子群已经定义，存在性与共轭性也已经证明。现在把 G 中全部西罗 P 子群组成一个有限集合，才引入计数记号。'),
f(String.raw`n_p=|\operatorname{Syl}_p(G)|`,'记这个集合的元素个数为 n 下标 P。这里的每个元素是一个子群；n 下标 P 不是子群的阶，也不是某类群元素的总数。'),
t('定理2.6.3：nₚ 整除 |G|，且模 p 余1','Theorem 2.6.3: nₚ divides |G| and is 1 modulo p.','第三西罗定理在这本教材中的原始陈述，是个数整除群阶，并且模 P 余一。之后还会从正规化子的指数式得到更强的整除条件。'),
f(String.raw`n_p\mid|G|,\qquad n_p\equiv1\pmod p`,'存在性已经说明个数至少为一，第三定理进一步限制它可以是哪几个数。这些条件是限制，不是凭空构造出具有任意候选个数的群。'),
t('推论3：在 |G|=pᵃm 下，nₚ∣m','Corollary 3: if |G|=pᵃm, then nₚ divides m.','教材把个数整除互素因子艾姆单列为推论三。实际解题时常把它与模 P 余一一起使用，但教材原始编号仍需区分。')],
'集合与个数的记号明确之后，陈述第三定理和计数推论。','|G|=12=3·4，p=3。','同时使用推论3与第三定理，列出n₃的候选值。','个数整除四，所以先有一、二、四。模三余一的只保留一和四。这里只得到候选值，尚未判断某个具体群取哪一个。',{4:{tone:'conclusion'},5:{tone:'conclusion'}}),
b('第三定理 — 正规化子与整除','Third theorem — normalizers and divisibility',360,third,[
t('G 通过共轭作用于 X=Sylₚ(G)','G acts on its Sylow subgroups by conjugation.','根据推论二，所有西罗子群彼此共轭，因此这个作用是传递的。固定一个西罗子群 P，它的轨道就是整个集合 X。'),
f(String.raw`g\cdot P=gPg^{-1},\qquad X=G\cdot P`,'共轭像还是相同阶数的子群，所以仍然是西罗子群，作用确实落在 X 内。作用的稳定子由哪些 g 满足共轭后仍等于 P 来确定。'),
f(String.raw`G_P=N_G(P)=\{g:gPg^{-1}=P\}`,'这个稳定子就是正规化子。它保持整个子群作为集合，并不要求逐个固定 P 中的每个元素，所以通常不同于中心化子。'),
f(String.raw`n_p=[G:N_G(P)],\qquad P\le N_G(P)`,'轨道稳定子定理给出个数的指数公式，因此个数首先整除 G 的阶。P 的每个元素作内共轭都保持 P，所以 P 包含在自己的正规化子里。'),
f(String.raw`m=[G:P]=n_p[N_G(P):P]\Longrightarrow n_p\mid m`,'再使用指数乘法公式，群到 P 的指数等于群到正规化子的指数，乘以正规化子到 P 的指数。前者总指数是艾姆，所以得到推论三。')],
'计数的整除部分来自共轭作用的一个轨道。','P为G的西罗p子群，|G|=pᵃm。','证明P≤N_G(P)，并推导nₚ整除m。','P 的内共轭保持它自己，所以 P 是正规化子的子群。共轭性给出 n 下标 P 等于 G 到正规化子的指数；指数乘法再给出它整除艾姆。',{5:{tone:'conclusion'}}),
b('第三定理 — 唯一不动点','Third theorem — the unique fixed point',300,third,[
t('固定 P₀∈Sylₚ(G)，让 P₀ 共轭作用于 X','Fix P₀ and let it act on X by conjugation.','现在把作用群缩小为固定的西罗子群 P 零。P 零本身当然是不动点；同余部分的关键是证明没有其他不动点。'),
f(String.raw`P\in X^{P_0}\Longrightarrow P_0\le N_G(P)`,'如果 P 是不动点，P 零中每个元素都通过共轭保持 P。因此 P 零包含在 P 的正规化子中。这个条件说的是正规化，不是逐元素交换。'),
t('P、P₀ 都是 N_G(P) 的西罗 p 子群','P and P₀ are Sylow subgroups of N_G(P).','正规化子中包含 P 和 P 零，二者阶都是 P 的 a 次方。正规化子是 G 的子群，它的阶不可能含有更高的 P 幂，所以这两者在正规化子中也都是西罗子群。'),
f(String.raw`\exists x\in N_G(P):P_0=xPx^{-1}=P`,'将已经证明的共轭推论用于正规化子，得到其中的某个 x 把 P 共轭成 P 零。由于 x 自身在正规化子里，它的共轭又必须保持 P，因此 P 零与 P 相等。'),
f(String.raw`X^{P_0}=\{P_0\}`,'不动点因此恰好是 P 零一个。这里没有假定正规化子是真子群，也没有使用第三定理自身。证明只依赖第二定理和有限群的阶数限制。')],
'要得到模 P 余一，需要把不动点数确定为一。','P₀、P均为G的西罗p子群，P₀≤N_G(P)。','说明为何它们也是正规化子的西罗子群，再证明P=P₀。','二者已有最高 P 幂阶，而正规化子包含于 G，不可能有更高的 P 幂阶子群。共轭推论在正规化子内给出 P 零是 P 的一个内共轭，而所有这些内共轭仍是 P，所以二者相等。',{5:{tone:'conclusion'}}),
b('第三定理 — 轨道求和得到同余','Third theorem — the congruence from orbits',280,third,[
t('P₀ 的非单点轨道大小被 p 整除','Nonsingleton P₀-orbits have size divisible by p.','P 零是 P 群，所以它在 X 上的每个轨道大小都是 P 的幂。除单点轨道外，所有轨道大小都被 P 整除。这与引理一所用的机制相同。'),
f(String.raw`|X|\equiv|X^{P_0}|\pmod p`,'对轨道大小求和，再模 P 约去非单点轨道。X 的大小就是西罗子群的个数，而上一板已经证明固定点集合只有一个元素。'),
f(String.raw`n_p\equiv1\pmod p`,'这就完成第三西罗定理的同余部分。与整除部分合起来，第三定理已证；与更强的整除式合起来，就是应用课将要使用的两条计数条件。'),
f(String.raw`n_p\mid m,\qquad n_p\equiv1\pmod p`,'解题时先列出艾姆的正约数，再筛出模 P 余一的数。筛选结果仍是候选集合，而不是断言每个数一定在某个指定群里实现。'),
t('存在、共轭、计数：应用课的三类输入','Existence, conjugacy and counts are the inputs for applications.','第一定理保证对象存在，第二定理与共轭推论把对象联系起来，第三定理与推论三限制对象个数。下一次课用这些信息研究正规子群及小阶群的结构。')],
'唯一不动点已经确定，同余式由轨道求和落下。','|G|=20=5·4，p=5。','由两条计数条件求 n₅，并说明本课已经得到什么。','个数整除四，又模五余一，只能等于一。计数结论说明五阶西罗子群唯一；应用课会进一步解释唯一性与正规性等价，以及哪些结构结论还需要额外论证。',{3:{tone:'conclusion'},4:{tone:'conclusion'}})
];
export const sylowPlan={id:'sylow-theorems',title:'西罗三大定理',course:'代数学 I',section:'2.6',duration:5700,periods:[{id:1,start:0,end:2700},{id:'break',start:2700,end:3000},{id:2,start:3000,end:5700}],scope:'按原教材证明第一、第二定理和共轭推论；第三定理证明为可跳过模块，完整陈述及推论3始终保留。',optionalProofOriginalIndices:[12,13,14],sources:[{label:'韩士安、林磊、杜荣《近世代数》第三版 §2.6，印刷页113—116',pdfPages:[125,126,127,128],sha256:TEXTBOOK_SHA256}]};
