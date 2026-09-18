const R=String.raw,pair=(zh,en)=>[zh,en];
const step=(zh,en,formulas,text)=>({title:pair(zh,en),formulas,text});
const entry=(id,no,title,formulas,proof,extra={})=>({id,no,kind:'definition',title,formulas,proof,graph:'simplicial-object',reference:'https://stacks.math.columbia.edu/tag/0169',...extra});
export const foundations=[
entry('simplex-category','1.1',pair('单纯范畴','The simplex category'),[
 R`[p]:=\{0<1<\cdots<p\}\quad(p\ge0)`,
 R`\operatorname{Hom}_{\Delta}([p],[q])`,
 R`:=\{\alpha:[p]\to[q]\mid i\le j\Rightarrow\alpha(i)\le\alpha(j)\}`
],[step('对象与态射','Objects and morphisms',[],pair(R`$\Delta$ 的对象是非空有限全序集 $[p]$；态射是弱保序映射，复合就是映射的通常复合。下标 $p$ 表示单纯次数，不是代数簇的维数。`,R`The objects of $\Delta$ are the nonempty finite ordered sets $[p]$. Morphisms are nondecreasing maps, with ordinary composition. The index $p$ is a simplicial degree, not the dimension of a variety.`))],{graph:'simplex-category',intro:pair('先定义组织各层对象及其结构映射的指标范畴。','First define the indexing category for the levels and their structure maps.')}),
entry('simplicial','1.2',pair('单纯概形','Simplicial scheme'),[
 R`X_\bullet:\Delta^{\mathrm{op}}\longrightarrow\mathrm{Sch}_{\mathbb C}`,
 R`X_p:=X_\bullet([p])`,
 R`\alpha:[p]\to[q]\quad\longmapsto\quad X(\alpha):X_q\to X_p`
],[step('反变函子的含义','Contravariant functoriality',[
 R`X(\mathrm{id}_{[p]})=\mathrm{id}_{X_p}`,
 R`X(\beta\circ\alpha)=X(\alpha)\circ X(\beta)`
],pair(R`这里 $\alpha:[p]\to[q]$、$\beta:[q]\to[r]$。$\mathrm{Sch}_{\mathbb C}$ 是复数域上概形及其态射组成的范畴。本文后续取各层为复代数簇或其有限不交并；单纯概形的定义本身没有光滑或射影条件。`,R`Here $\alpha:[p]\to[q]$ and $\beta:[q]\to[r]$. The category $\mathrm{Sch}_{\mathbb C}$ consists of schemes over the complex numbers and their morphisms. Later we take the levels to be complex varieties or finite disjoint unions of them. The definition itself imposes no smoothness or projectivity.`))],{intro:pair('复数域上的单纯概形，就是下面的反变函子。','A simplicial scheme over the complex numbers is the following contravariant functor.')}),
entry('faces-degeneracies','1.3',pair('面映射与退化映射','Faces and degeneracies'),[
 R`d_i^{(p)}:X_p\longrightarrow X_{p-1}\quad(0\le i\le p,\ p\ge1)`,
 R`s_i^{(p)}:X_p\longrightarrow X_{p+1}\quad(0\le i\le p,\ p\ge0)`
],[step('面映射','Faces',[
 R`\delta_i^{(p)}:[p-1]\hookrightarrow[p]`,
 R`\delta_i^{(p)}(k)=\begin{cases}k&k<i,\\k+1&k\ge i,\end{cases}\qquad d_i^{(p)}:=X(\delta_i^{(p)})`
],pair(R`$\delta_i^{(p)}$ 跳过顶点 $i$。函子反转方向，所以 $d_i^{(p)}$ 降低单纯次数。这里 $\delta_i^{(p)}$ 是有限有序集间的映射，区别于第二节的上链微分 $\delta_1,\delta_2$。`,R`The injection $\delta_i^{(p)}$ skips vertex $i$. Contravariance makes $d_i^{(p)}$ lower simplicial degree. These maps of ordered sets are distinct from the cochain differentials $\delta_1,\delta_2$ in Section 2.`)),step('退化映射','Degeneracies',[
 R`\sigma_i^{(p)}:[p+1]\twoheadrightarrow[p]`,
 R`\sigma_i^{(p)}(k)=\begin{cases}k&k\le i,\\k-1&k>i,\end{cases}\qquad s_i^{(p)}:=X(\sigma_i^{(p)})`
],pair(R`$\sigma_i^{(p)}$ 把 $i,i+1$ 合并。其反向像 $s_i^{(p)}$ 增加单纯次数。`,R`The surjection $\sigma_i^{(p)}$ identifies $i$ and $i+1$. Its contravariant image $s_i^{(p)}$ raises simplicial degree.`))]),
entry('simplicial-identities','1.4',pair('单纯恒等式','Simplicial identities'),[
 R`d_i d_j=d_{j-1}d_i\quad(i<j)`,
 R`s_i s_j=s_{j+1}s_i\quad(i\le j)`,
 R`d_i s_j=\begin{cases}s_{j-1}d_i&i<j,\\\mathrm{id}&i=j\ \text{or}\ i=j+1,\\s_jd_{i-1}&i>j+1.\end{cases}`
],[step('由有序集映射得到恒等式','Identities from maps of ordered sets',[
 R`\delta_j^{(p)}\delta_i^{(p-1)}=\delta_i^{(p)}\delta_{j-1}^{(p-1)}\quad(i<j)`
],pair(R`两边都是跳过 $i,j$ 的保序单射；作用 $X$ 并反转复合顺序即得面关系。用 1.3 的分段公式逐点计算，合并两个位置得到退化关系，先跳过再合并得到混合关系；当被跳过的位置是刚合并的两个位置之一时，复合为恒等映射。`,R`Both sides are the increasing injection omitting $i,j$. Apply $X$ and reverse composition to obtain the face identity. Evaluate the piecewise formulas of 1.3: two identifications give the degeneracy identity, while an omission and an identification give the mixed identities. Omitting either of the two identified positions gives the identity map.`)),step('次数与边界范围','Degrees and boundary cases',[
 R`d_i^{(p-1)}d_j^{(p)}=d_{j-1}^{(p-1)}d_i^{(p)}\quad(p\ge2,\ 0\le i<j\le p)`,
 R`s_i^{(p+1)}s_j^{(p)}=s_{j+1}^{(p+1)}s_i^{(p)}\quad(p\ge0,\ 0\le i\le j\le p)`
],pair(R`左侧简写省略了次数上标；每个式子仅在复合有定义时使用。混合式中 $s_j$ 的源为 $X_p$，$0\le j\le p$，随后 $0\le i\le p+1$；$p=0$ 时只有两个恒等分支。`,R`The abbreviated statements suppress degree superscripts and apply whenever the composites are defined. In the mixed identity, $s_j$ starts at $X_p$, with $0\le j\le p$ and then $0\le i\le p+1$. When $p=0$, only the two identity cases occur.`))],{kind:'proposition',intro:pair('以下省略次数上标，复合按从右到左理解。','Degree superscripts are suppressed below; composition is read from right to left.'),statementSetup:pair(R`设 $X_\bullet$ 是 1.2 中的单纯概形，$d_i,s_i$ 如 1.3。则只要复合有定义，就有以下恒等式。`,R`Let $X_\bullet$ be a simplicial scheme as in 1.2, with $d_i,s_i$ as in 1.3. Then the following identities hold whenever the composites are defined.`)}),
entry('split-degeneracies','1.5',pair('退化映射的左逆','Left inverses of degeneracies'),[
 R`d_j^{(p+1)}s_j^{(p)}=\mathrm{id}_{X_p}`,R`d_{j+1}^{(p+1)}s_j^{(p)}=\mathrm{id}_{X_p}`
],[step('分裂单态射','Split monomorphisms',[
 R`s_j^{(p)}u=s_j^{(p)}v\quad\Longrightarrow\quad u=v`
],pair(R`两个左逆等式由 1.4 的混合关系得到。取任意概形 $T$ 及 $u,v:T\to X_p$。在等式两边左复合 $d_j^{(p+1)}$，便得到 $u=v$。因此 $s_j^{(p)}$ 是分裂单态射；两个相邻面映射都是它的左逆。`,R`The two left-inverse identities follow from the mixed relations in 1.4. Take a scheme $T$ and morphisms $u,v:T\to X_p$. Compose the equality on the left with $d_j^{(p+1)}$ to obtain $u=v$. Thus $s_j^{(p)}$ is a split monomorphism; both adjacent face maps are left inverses.`))],{kind:'proposition',statementSetup:pair(R`设 $X_\bullet$ 为单纯概形，$p\ge0$ 且 $0\le j\le p$。则退化映射 $s_j^{(p)}$ 有以下两个左逆，因而是分裂单态射。`,R`Let $X_\bullet$ be a simplicial scheme, $p\ge0$, and $0\le j\le p$. Then $s_j^{(p)}$ has the two left inverses below and is a split monomorphism.`)}),
entry('simplicial-morphism','1.6',pair('单纯态射与自映射','Simplicial morphisms and endomorphisms'),[
 R`f_\bullet:X_\bullet\longrightarrow Y_\bullet,\qquad f_p:X_p\to Y_p`,
 R`d_{i,Y}^{(p)}f_p=f_{p-1}d_{i,X}^{(p)}`,R`s_{i,Y}^{(p)}f_p=f_{p+1}s_{i,X}^{(p)}`
],[step('自然变换','Natural transformation',[R`Y(\alpha)f_q=f_pX(\alpha)\quad(\alpha:[p]\to[q])`],pair(R`单纯态射就是两个反变函子间的自然变换。每个保序映射都由跳过与合并映射复合而成，所以只须检查面与退化映射的交换关系。当 $Y_\bullet=X_\bullet$ 时得到单纯自映射；不要求其可逆。`,R`A simplicial morphism is a natural transformation. Every nondecreasing map is a composite of omissions and identifications, so it suffices to check compatibility with faces and degeneracies. Taking $Y_\bullet=X_\bullet$ gives a simplicial endomorphism; invertibility is not required.`))],{graph:'simplicial'}),
entry('cech-nerve','1.7',pair('Čech 神经','The Čech nerve'),[
 R`u:U\to S`,R`X_p:=\underbrace{U\times_S\cdots\times_SU}_{p+1\ \text{factors}}`,
 R`\begin{gathered}d_i:(u_0,\ldots,u_p)\\\longmapsto(u_0,\ldots,\widehat{u_i},\ldots,u_p)\end{gathered}`,
 R`\begin{gathered}s_i:(u_0,\ldots,u_p)\\\longmapsto(u_0,\ldots,u_i,u_i,\ldots,u_p)\end{gathered}`
],[step('用纤维积构造','Construction with fibre products',[
 R`X(\alpha)(u_0,\ldots,u_q)=(u_{\alpha(0)},\ldots,u_{\alpha(p)})`
],pair(R`设 $u$ 是复概形态射。上述坐标式在每个测试概形的点上理解；投影与对角态射使它们成为概形态射。选取坐标与复合相容，故定义反变函子。此构造不要求 $u$ 是覆盖，也没有在此断言上同调下降。`,R`Let $u$ be a morphism of complex schemes. Interpret the coordinate formulas on points valued in any test scheme. Projections and diagonals make them scheme morphisms. Selecting coordinates respects composition, so this defines a contravariant functor. The construction does not require $u$ to be a cover and does not assert cohomological descent.`))],{kind:'example',graph:'cech-nerve'})
];
