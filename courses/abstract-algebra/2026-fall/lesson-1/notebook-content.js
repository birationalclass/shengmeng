/* References follow Han–Lin–Du, Modern Algebra, third edition. */
(()=>{
  const item=(topic,ref,title,formula,text,extra={})=>({topic,ref,title,formula,text,...extra});
  window.LessonNotebookContent={
    '1.1':[
      item('relation',['定义 1.1.1','Definition 1.1.1'],['关系','Relations'],'a R b  ⟺  (a, b) ∈ R',[
        '在非空集合 S 中，对任意两个元素 a、b，都能确定条件 R 是否成立，就得到 S 上的一个关系。也可用有序对的集合 R ⊆ S × S 表示。',
        'A relation on a nonempty set S specifies, for every pair a, b, whether a R b holds. Equivalently, it is a subset R of S × S.'
      ]),
      item('relation',['定义 1.1.1','Definition 1.1.1'],['关系的函数表示','Relations as functions'],'R : S × S → {0, 1}<br>或 R : S × S → {F, T}',[
        '把关系看成一个判断函数：R(a,b) = 1（或 T）表示 a 与 b 有关系，R(a,b) = 0（或 F）表示没有关系。其中 F = False，T = True。这与用有序对的集合定义关系完全等价。',
        'A relation can be viewed as a truth-valued function: R(a,b) = 1 (or T) means that a is related to b; R(a,b) = 0 (or F) means it is not. Here F = False and T = True. This is equivalent to describing a relation as a set of ordered pairs.'
      ],{extension:true,formulaEn:'R : S × S → {0, 1}<br>or R : S × S → {F, T}',detail:[
        '函数形式便于扩展：把值域换成 [0,1]，得到 R : S × S → [0,1]，就能表达关系的程度，而不只回答“有”或“无”。在明确的随机模型中，也可以令 R(a,b) 表示事件“a 与 b 有关系”的概率，从而与概率论联系起来。一般的关系程度或隶属度不自动等于概率，概率解释需要相应的随机模型。',
        'The function viewpoint is easy to extend: R : S × S → [0,1] can express a degree of relatedness instead of only yes or no. In a specified random model, R(a,b) may instead be the probability of the event that a is related to b, connecting the idea to probability theory. A general degree or membership value is not automatically a probability; that interpretation requires a random model.'
      ]}),
      item('relation',['定义 1.1.2','Definition 1.1.2'],['等价关系','Equivalence relations'],'a ∼ a<br>a ∼ b ⇒ b ∼ a<br>a ∼ b, b ∼ c ⇒ a ∼ c',[
        'S 上的关系同时具有反身性、对称性和传递性，称为等价关系。三个条件都须对集合中的所有相应元素成立。',
        'An equivalence relation is reflexive, symmetric and transitive. Each condition must hold for every relevant choice of elements in S.'
      ]),
      item('quotient',['定义 1.1.3','Definition 1.1.3'],['等价类与商集','Classes and quotients'],'[a] = {x ∈ S : x ∼ a}<br>S / ∼ = {[a] : a ∈ S}',[
        '等价类 [a] 是与 a 等价的全部元素组成的子集。全部不同的等价类组成商集。右图以模 m 的同余关系为例：类是商集的元素。',
        'The class [a] consists of all elements equivalent to a. The quotient is the set of distinct classes. The diagram uses congruence modulo m: each whole class becomes one quotient element.'
      ]),
      item('partition',['定义 1.1.4','Definition 1.1.4'],['集合的分类','Partitions'],'S = ⋃ Sᵢ<br>Sᵢ ≠ ∅,  Sᵢ ∩ Sⱼ = ∅  (i ≠ j)',[
        '把 S 写成若干两两不相交的非空子集的并，就得到一种分类。每个元素恰好属于其中一个类：不遗漏，也不重复。',
        'A partition expresses S as a union of pairwise disjoint nonempty subsets. Every element belongs to exactly one block.'
      ]),
      item('partition',['定理 1.1.1','Theorem 1.1.1'],['等价关系与分类的对应','Relations and partitions'],'a ∼ b  ⟺  [a] = [b]',[
        '每个等价关系的全部等价类构成一个分类。反过来，每个分类都确定一个等价关系：两元素等价当且仅当它们属于同一类。这两个构造互为逆过程。',
        'The distinct equivalence classes form a partition. Conversely, a partition defines an equivalence relation by membership in the same block. The two constructions are inverse to each other.'
      ],{exposition:true}),
      item('check',['§1.1','§1.1'],['自测','Self-check'],'',[
        '先独立判断，再选择答案。每题标明教材来源与难度；选择后查看理由并逐步展开证明。',
        'Make your own judgment before choosing an answer. Each question identifies its textbook source and difficulty; then review the explanation and proof steps.'
      ])
    ],
    '1.2':[
      item('operation',['定义 1.2.1','Definition 1.2.1'],['代数运算','Algebraic operations'],'A × A → A<br>(a, b) ↦ a · b',[
        '对非空集合 A 中的每一对元素，运算法则都给出唯一的 A 中元素。若元素是等价类，还须验证结果不依赖代表元的选择。',
        'An operation assigns a unique element of A to each ordered pair in a nonempty set A. For equivalence classes, the result must also be independent of representatives.'
      ]),
      item('axioms',['定义 1.2.2','Definition 1.2.2'],['群','Groups'],'(ab)c = a(bc)<br>ea = ae = a<br>aa⁻¹ = a⁻¹a = e',[
        '非空集合 G 配备代数运算。若满足结合律，存在对所有元素有效的双侧单位元 e，且每个元素都有双侧逆元，则称 G 为群。交换律是额外条件。',
        'A group is a nonempty set with an associative operation, a two-sided identity e, and a two-sided inverse for every element. Commutativity is an additional condition.'
      ]),
      item('symmetry',['§1.2 · 几何演示','§1.2 · Geometric example'],['三角形的对称群','Symmetries of a triangle'],'D₃ = {e, r, r², s, rs, r²s}',[
        '群的元素也可以是变换，群运算是变换的复合。比较先旋转后反射、先反射后旋转：相同的轮廓不意味着相同的变换。',
        'Group elements may be transformations, with composition as the operation. Compare rotation followed by reflection with the reverse order: the same outline need not mean the same transformation.'
      ]),
      item('properties',['定理 1.2.1(1)','Theorem 1.2.1(1)'],['单位元唯一','Uniqueness of the identity'],'e = ef = f',[
        '设 G 为群。如果 e、f 都是 G 的双侧单位元，则 e = f。因此群的单位元唯一。',
        'If e and f are both two-sided identities of a group G, then e = f. Thus the identity is unique.'
      ],{proof:0}),
      item('properties',['定理 1.2.1(2)','Theorem 1.2.1(2)'],['逆元唯一','Uniqueness of inverses'],'b = b(ac) = (ba)c = c',[
        '设 G 为群，a ∈ G。如果 ab = ba = e 且 ac = ca = e，则 b = c。因此每个元素的逆元唯一。',
        'For a ∈ G, if ab = ba = e and ac = ca = e, then b = c. Each element therefore has a unique inverse.'
      ],{proof:1}),
      item('properties',['定理 1.2.1(3)','Theorem 1.2.1(3)'],['逆元的逆元','The inverse of an inverse'],'(a⁻¹)⁻¹ = a',[
        '设 G 为群。对任意 a ∈ G，a⁻¹ 的逆元就是 a。先验证 a 满足逆元的两侧等式，再使用逆元唯一性。',
        'In a group G, the inverse of a⁻¹ is a. Verify the two inverse equations, then use uniqueness of the inverse.'
      ],{proof:2}),
      item('properties',['定理 1.2.1(4)','Theorem 1.2.1(4)'],['乘积的逆元','The inverse of a product'],'(ab)⁻¹ = b⁻¹a⁻¹',[
        '设 G 为群。对任意 a、b ∈ G，乘积 ab 的逆元是 b⁻¹a⁻¹。撤销复合运算时，因子的次序反转。',
        'For any a, b in a group G, the inverse of ab is b⁻¹a⁻¹. Reversing a composite operation reverses the order of its factors.'
      ],{proof:3}),
      item('properties',['定理 1.2.1(5)','Theorem 1.2.1(5)'],['消去律','Cancellation'],'ab = ac ⇒ b = c<br>ba = ca ⇒ b = c',[
        '群中左消去律和右消去律都成立。要消去哪个因子，就在等式两边的同一侧乘上它的逆元。',
        'Both cancellation laws hold in a group. Multiply both sides of the equation on the appropriate side by the inverse of the factor being cancelled.'
      ],{proof:4}),
      item('properties',['定理 1.2.2','Theorem 1.2.2'],['群方程的唯一解','Unique solutions of group equations'],'ax = b  ⇒  x = a⁻¹b<br>ya = b  ⇒  y = ba⁻¹',[
        '设 G 为群。对任意 a、b ∈ G，ax = b 和 ya = b 各有唯一解。解的存在性由代入验证，唯一性由消去律保证。',
        'For any a, b ∈ G, each equation ax = b and ya = b has a unique solution. Substitution proves existence and cancellation proves uniqueness.'
      ],{proof:5}),
      item('powers',['§1.2 · 第 14—15 页','§1.2 · pp. 14–15'],['方幂与指数法则','Integer powers'],'a⁰ = e,  a⁻ⁿ = (a⁻¹)ⁿ<br>aᵐaⁿ = aᵐ⁺ⁿ,  (aᵐ)ⁿ = aᵐⁿ',[
        '正整数幂表示重复相乘，负整数幂通过逆元定义。对同一元素，指数法则对所有整数成立；(ab)ⁿ = aⁿbⁿ 则不能随意使用。',
        'Positive powers repeat multiplication; negative powers use inverses. The exponent laws hold for all integer powers of one element. The identity (ab)ⁿ = aⁿbⁿ cannot be used in general.'
      ]),
      item('criteria',['定理 1.2.3','Theorem 1.2.3'],['同侧单位元与逆元','One-sided identity and inverses'],'ea = a,  a′a = e',[
        '设 G 为非空集合，具有满足结合律的代数运算。如果存在同一个左单位元 e，且每个 a ∈ G 都存在左逆元 a′，则 G 为群。反过来，群必满足这些条件。',
        'Let G be nonempty with an associative operation. If it has a common left identity e and each a has a left inverse a′, then G is a group. Conversely, every group satisfies these conditions.'
      ],{criterion:0}),
      item('criteria',['定理 1.2.4','Theorem 1.2.4'],['用群方程判别','Solvability criterion'],'ax = b,  ya = b',[
        '设非空集合 G 具有满足结合律的代数运算。G 是群，当且仅当对所有 a、b ∈ G，上述两个方程都在 G 中有解。这里不预先假设解唯一。',
        'Let G be nonempty with an associative operation. It is a group exactly when both equations are solvable in G for all a, b ∈ G. Uniqueness is not assumed.'
      ],{criterion:1}),
      item('criteria',['例 11 · §1.2','Example 11 · §1.2'],['有限集合的消去律','Cancellation on a finite set'],'|G| < ∞  +  左、右消去律',[
        '非空有限集合 G 配备满足结合律的代数运算。如果左右消去律都成立，则 G 是群。有限性不可删去。',
        'A nonempty finite set with an associative operation and both cancellation laws is a group. Finiteness is essential.'
      ],{criterion:2,formulaEn:'|G| < ∞  +  left and right cancellation'}),
      item('check',['§1.2','§1.2'],['自测','Self-check'],'',[
        '用例子检验群的定义、基本性质与判别。先独立选择答案，再读理由与逐步证明。',
        'Test the definition, properties and criteria through examples. Choose an answer independently, then review the reasoning and proof steps.'
      ])
    ]
  };
})();
