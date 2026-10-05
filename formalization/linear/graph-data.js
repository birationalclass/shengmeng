export const nodes=[
  {
    "id": "reduction",
    "title": [
      "Reduction controls multiplication",
      "约化控制乘法作用"
    ],
    "summary": [
      "The action on Ann(N) factors through A/N.",
      "Ann(N) 上的作用经 A/N 因子化。"
    ],
    "formula": "a x=q(a)x",
    "deps": [],
    "x": 20,
    "y": 40,
    "decl": "multiplication_factors_through_reduction",
    "file": "Linear/Reduction.lean",
    "scope": "done",
    "statement": [
      [
        "Let B and A be commutative rings, and A a B-algebra. Let q:A→B be a B-algebra map whose kernel is the nilradical N. If Nx=0, then multiplication by a∈A on x only depends on q(a).",
        "设 B、A 为交换环，A 为 B-代数，q:A→B 为 B-代数同态且 ker(q)=N。若 Nx=0，则 a∈A 对 x 的乘法作用只依赖 q(a)。"
      ]
    ],
    "formulas": [
      "a x=\\operatorname{algMap}(q(a))x"
    ],
    "proof": [
      [
        "Subtract the reduced lift",
        "相减约化提升",
        "a−algMap(q(a)) belongs to ker(q)=N.",
        "a−algMap(q(a)) 属于 ker(q)=N。"
      ],
      [
        "Use annihilation",
        "使用湮灭关系",
        "Multiplying this difference by x gives zero. The desired equality follows.",
        "这个差乘上 x 为零，得到所需等式。"
      ]
    ]
  },
  {
    "id": "pairing",
    "title": [
      "Closed-fiber Gorenstein input",
      "闭纤维 Gorenstein 输入"
    ],
    "summary": [
      "Produce a functional with a nondegenerate reduced Gram matrix.",
      "构造约化 Gram 矩阵非退化的泛函。"
    ],
    "formula": "\\det\\overline{G}_{\\ell}\\ne0",
    "deps": [],
    "x": 20,
    "y": 230,
    "file": "Linear/PairingMatrix.lean",
    "scope": "assumption",
    "statement": [
      [
        "For the finite flat complete intersection, construct a finite B-basis and a B-linear functional ℓ whose multiplication Gram matrix is nondegenerate modulo m_B. The remaining geometric-algebraic input is the Gorenstein property of the Artinian complete-intersection fiber and lifting its functional.",
        "对有限平坦完全交，构造有限 B-基及 B-线性泛函 ℓ，使乘法 Gram 矩阵模 m_B 后非退化。尚待形式化的输入是 Artin 完全交纤维的 Gorenstein 性质及其泛函的提升。"
      ]
    ],
    "formulas": [
      "G_{\\ell,ij}=\\ell(b_jb_i),\\qquad\\det\\overline{G}_{\\ell}\\ne0"
    ],
    "proof": [
      [
        "Artinian fiber",
        "Artin 纤维",
        "Prove the complete-intersection closed fiber is Gorenstein and select a functional with nondegenerate multiplication pairing. This still remains open.",
        "证明完全交闭纤维是 Gorenstein，并选择乘法配对非退化的泛函；该步骤仍待证明。"
      ],
      [
        "Lift the functional",
        "提升泛函",
        "Finite freeness lets a basis and the functional lift to B. The following matrix card now proves the determinant criterion for the lifted pairing.",
        "有限自由性允许将基和泛函提升到 B。后续矩阵卡片已证明提升配对的行列式判据。"
      ]
    ]
  },
  {
    "id": "jacobian",
    "title": [
      "Identify the Jacobian",
      "识别 Jacobian"
    ],
    "summary": [
      "Prove that the specified determinant annihilates N and is a primitive generator.",
      "证明指定行列式湮灭 N，且是本原生成元。"
    ],
    "formula": "\\Delta=\\det(\\partial H_i/\\partial z_j)",
    "deps": [],
    "x": 20,
    "y": 420,
    "file": "Linear/Target.lean",
    "scope": "assumption",
    "statement": [
      [
        "Δ is the actual determinant of the formal partial derivatives of H. It is not an arbitrary element chosen from Ann(N). The generic-fiber Scheja–Storch theorem and nonvanishing of this determinant remain open. The general primitive-generator implication is checked in a separate card.",
        "Δ 是 H 的形式偏导矩阵的实际行列式，并非从 Ann(N) 任意选取的元素。泛纤维 Scheja–Storch 定理及此行列式的非零性尚未完成；一般的本原生成元蕴含已在独立卡片中验证。"
      ]
    ],
    "formulas": [
      "N\\Delta=0,\\qquad\\Delta\\notin\\mathfrak m_B A"
    ],
    "proof": [
      [
        "Generic fiber",
        "泛纤维",
        "Pass to Frac(B), apply the Jacobian socle theorem, and descend annihilation using B-flatness.",
        "转到 Frac(B)，使用 Jacobian socle 定理，再由 B-平坦性下降湮灭关系。"
      ],
      [
        "Closed fiber",
        "闭纤维",
        "Show Δ survives in A/m_B A. In a rank-one annihilator this makes its scalar coefficient a unit. Neither step is being assumed proved by the target definition.",
        "证明 Δ 在 A/m_B A 中非零，从而其秩一湮灭子中的系数是单位。目标的定义不构成这些步骤的证明。"
      ]
    ]
  },
  {
    "id": "duality",
    "title": [
      "A scalar generator of Ann(N)",
      "Ann(N) 的标量生成元"
    ],
    "summary": [
      "Verified implication once a perfect multiplication pairing is supplied.",
      "给定完美乘法配对后验证的蕴含。"
    ],
    "formula": "\\operatorname{Ann}_A(N)=B\\eta",
    "deps": [
      "reduction",
      "matrix"
    ],
    "x": 335,
    "y": 40,
    "decl": "annihilator_iff_scalar_multiple",
    "file": "Linear/Duality.lean",
    "scope": "conditional",
    "statement": [
      [
        "Given q:A→B and an explicit perfect multiplication pairing Ψ, define η=Ψ⁻¹(q). Then ker(q)η=0 and every element annihilating ker(q) is a B-scalar multiple of η. The pairing-existence and Jacobian-identification steps are still required for the manuscript theorem.",
        "给定 q:A→B 及显式完美乘法配对 Ψ，定义 η=Ψ⁻¹(q)。则 ker(q)η=0，且湮灭 ker(q) 的每个元素均为 η 的 B-标量倍。要得到原稿定理，仍须配对存在性及 Jacobian 识别。"
      ]
    ],
    "formulas": [
      "\\eta=\\Psi^{-1}(q),\\qquad x=\\ell(x)\\eta,\\qquad\\ell(\\eta)=1"
    ],
    "proof": [
      [
        "The dual generator",
        "对偶生成元",
        "By construction ℓ(ηa)=q(a), so ℓ(η)=1.",
        "按构造 ℓ(ηa)=q(a)，故 ℓ(η)=1。"
      ],
      [
        "Annihilation",
        "湮灭",
        "For n∈ker(q), the perfect pairing of nη with every a is q(na)=0; injectivity forces nη=0.",
        "对 n∈ker(q)，nη 与任意 a 的配对均为 q(na)=0，单射性迫使 nη=0。"
      ],
      [
        "Generation",
        "生成性",
        "For Nx=0, write ax=q(a)x. Then Ψ(x)=ℓ(x)q, so x=ℓ(x)η.",
        "若 Nx=0，则 ax=q(a)x，从而 Ψ(x)=ℓ(x)q，即 x=ℓ(x)η。"
      ]
    ]
  },
  {
    "id": "parameters",
    "title": [
      "Change the parameter lifts",
      "改变参数提升"
    ],
    "summary": [
      "Construct the same duality over the new parameter ring B′.",
      "在新的参数环 B′ 上构造同一对偶性。"
    ],
    "formula": "B^{\\prime}=\\mathbb C[[T_1,\\ldots,T_r]]",
    "deps": [
      "matrix",
      "jacobian",
      "primitive"
    ],
    "x": 335,
    "y": 420,
    "file": "Linear/Target.lean",
    "scope": "assumption",
    "statement": [
      [
        "For arbitrary τᵢ whose reduced images form parameters, construct the B′-algebra structure Tᵢ↦τᵢ, prove finite freeness over B′, and obtain a split inclusion B′Δ↪A. These bridges are not yet proved in Lean.",
        "对于约化后形成参数系的任意 τᵢ，构造 Tᵢ↦τᵢ 的 B′-代数结构，证明 B′ 上有限自由，再得到 B′Δ↪A 的分裂单射。这些桥接尚待 Lean 证明。"
      ]
    ],
    "formulas": [
      "A/(\\tau_1,\\ldots,\\tau_r)"
    ],
    "proof": [
      [
        "Parameter ring",
        "参数环",
        "Completeness supplies evaluation of formal series at τᵢ. Prove B′→A/N is an isomorphism.",
        "完备性给出形式级数在 τᵢ 的代入，证明 B′→A/N 为同构。"
      ],
      [
        "Freeness and splitting",
        "自由性与分裂",
        "Use the nilpotent filtration and Cohen–Macaulay parameter theorem, then relative duality over B′.",
        "使用幂零滤过及 Cohen–Macaulay 参数定理，再在 B′ 上应用相对对偶。"
      ]
    ]
  },
  {
    "id": "quotient",
    "title": [
      "Nonzero after quotienting",
      "取商后仍非零"
    ],
    "summary": [
      "A linear retraction proves that the dual generator survives an admissible quotient.",
      "线性左逆保证对偶生成元在满足条件的商中仍非零。"
    ],
    "formula": "\\overline\\eta\\ne0",
    "deps": [
      "duality"
    ],
    "x": 335,
    "y": 610,
    "decl": "dualGenerator_quotient_nonzero",
    "file": "Linear/Duality.lean",
    "scope": "conditional",
    "statement": [
      [
        "Given the pairing, an ideal J⊂A and a proper ideal m⊂B such that ℓ(J)⊂m, the image of η in A/J is nonzero. This is a general conditional theorem. Applying it to arbitrary parameter lifts and the specified Δ requires the preceding open bridges.",
        "给定配对、J⊂A 及真理想 m⊂B，若 ℓ(J)⊂m，则 η 在 A/J 的像非零。这是一般条件式定理；应用于任意参数提升及指定 Δ 仍需前述未完成桥接。"
      ]
    ],
    "formulas": [
      "\\ell(\\eta)=1,\\qquad\\ell(J)\\subseteq\\mathfrak m\\ \\Longrightarrow\\ \\eta\\notin J"
    ],
    "proof": [
      [
        "A retraction",
        "左逆",
        "The functional satisfies ℓ(bη)=b, so the cyclic submodule is split.",
        "泛函满足 ℓ(bη)=b，故循环子模分裂。"
      ],
      [
        "Survival in the quotient",
        "商中非零",
        "If η belonged to J, its image under ℓ would be 1∈m, contradicting properness.",
        "若 η∈J，则 ℓ(η)=1∈m，与真理想矛盾。"
      ]
    ]
  },
  {
    "id": "primitive",
    "title": [
      "A primitive element generates",
      "本原元素生成湮灭子"
    ],
    "summary": [
      "The local-ring coefficient argument is checked; Jacobian primitivity remains open.",
      "局部环系数论证已验证；Jacobian 的本原性待证。"
    ],
    "formula": "N\\delta=0,\\ \\overline\\delta\\ne0\\Rightarrow\\operatorname{Ann}(N)=B\\delta",
    "deps": [
      "duality",
      "jacobian",
      "generic"
    ],
    "x": 335,
    "y": 230,
    "decl": "primitive_annihilator_generates",
    "file": "Linear/Primitive.lean",
    "scope": "conditional",
    "statement": [
      [
        "Given the perfect pairing over a local base B, suppose δ annihilates ker(q) and does not belong to m_B A. Then every element annihilating ker(q) is a B-scalar multiple of δ. This proves the coefficient step, with the two properties of δ supplied explicitly.",
        "给定局部底环 B 上的完美配对，假设 δ 湮灭 ker(q)，且 δ 不属于 m_B A。则湮灭 ker(q) 的每个元素都是 δ 的 B-标量倍。这验证了系数步骤；δ 的两个性质仍作为显式假设。"
      ]
    ],
    "formulas": [
      "\\delta=\\ell(\\delta)\\eta",
      "\\delta\\notin\\mathfrak m_B A\\ \\Longrightarrow\\ \\ell(\\delta)\\in B^\\times"
    ],
    "proof": [
      [
        "Coefficient is a unit",
        "系数是单位",
        "Write δ=ℓ(δ)η using duality. If ℓ(δ) were not a unit, it would belong to the maximal ideal, forcing δ∈m_B A.",
        "由对偶性写 δ=ℓ(δ)η。若 ℓ(δ) 不是单位，它属于极大理想，迫使 δ∈m_B A。"
      ],
      [
        "Change the generator",
        "更换生成元",
        "The unit ℓ(δ) identifies Bδ with Bη. For x annihilating the kernel, x=ℓ(x)ℓ(δ)⁻¹δ.",
        "单位 ℓ(δ) 保证 Bδ=Bη；对湮灭核的 x，有 x=ℓ(x)ℓ(δ)⁻¹δ。"
      ]
    ]
  },
  {
    "id": "doublepoint",
    "title": [
      "The actual quadratic Jacobian",
      "真正的二次 Jacobian"
    ],
    "summary": [
      "A proved family: B[[z]]/(z²), with Δ=2z and 2 invertible.",
      "已证明的族：B[[z]]/(z²)，Δ=2z，2 可逆。"
    ],
    "formula": "A=B[[z]]/(z^2),\\quad\\operatorname{Ann}(N)=B(2z)",
    "deps": [],
    "x": 20,
    "y": 610,
    "decl": "quadratic_powerSeries_jacobian_annihilator",
    "file": "Linear/FirstJet.lean",
    "scope": "done",
    "statement": [
      [
        "Let B be a reduced commutative ring in which 2 is a unit. For the actual power-series quotient A=B[[z]]/(z²), Lean proves Ann_A(√0)=BΔ, where Δ is the class of the formal derivative of the defining equation z². The first-jet algebra isomorphism and explicit perfect pairing are proved, not assumed. This concrete family does not prove the universal lemma or its arbitrary-parameter-lift conclusion.",
        "设 B 为约化交换环，且 2 可逆。对真正的形式幂级数商环 A=B[[z]]/(z²)，Lean 证明 Ann_A(√0)=BΔ；Δ 是定义方程 z² 的形式导数的类。第一阶 jet 代数同构及显式完美配对均已证明，而非假设。此具体族未证明一般引理或任意参数提升的结论。"
      ]
    ],
    "formulas": [
      "f\\longmapsto f_0+f_1\\varepsilon,\\qquad\\ker=(z^2)",
      "B[[z]]/(z^2)\\simeq_B B\\oplus B\\varepsilon",
      "\\Delta=2\\varepsilon,\\qquad\\ell(\\varepsilon a)=a_0"
    ],
    "proof": [
      [
        "An actual presentation",
        "真正的表示",
        "The first-jet algebra map is surjective. Its kernel is (z²), because divisibility by z² is equivalent to vanishing constant and linear coefficients. The first isomorphism theorem gives the B-algebra equivalence.",
        "第一阶 jet 代数映射满射；核为 (z²)，因为被 z² 整除等价于常数及一次系数均为零。第一同构定理给出 B-代数同构。"
      ],
      [
        "The actual Jacobian",
        "真正的 Jacobian",
        "The formal derivative of z² maps to 2ε. Since 2 is a unit and ε generates the annihilator in the square-zero extension, this derivative class generates the quotient-ring annihilator.",
        "z² 的形式导数映到 2ε。由于 2 可逆，且 ε 生成平方零扩张中的湮灭子，导数的类生成商环的湮灭子。"
      ],
      [
        "Residue to evaluation",
        "留数转点值",
        "The ε-coefficient functional is a constructed perfect pairing; it satisfies ℓ(εa)=a.fst.",
        "ε 系数泛函的完美配对已经构造；满足 ℓ(εa)=a.fst。"
      ]
    ]
  },
  {
    "id": "matrix",
    "title": [
      "Lift the perfect pairing",
      "提升完美配对"
    ],
    "summary": [
      "Construct the pairing from a finite basis and a nonzero reduced Gram determinant.",
      "由有限基及非零约化行列式构造配对。"
    ],
    "formula": "\\det\\overline{G}_{\\ell}\\ne0\\Rightarrow A\\simeq A^{\\vee}",
    "file": "Linear/PairingMatrix.lean",
    "decl": "exists_perfectPairing_of_residueDet_ne_zero",
    "scope": "conditional",
    "deps": [
      "pairing"
    ],
    "statement": [
      [
        "Over a local base B, given a finite B-basis of A and a B-linear functional ℓ, if the Gram determinant is nonzero in B/m_B, Lean constructs the perfect multiplication pairing with functional ℓ. Existence of the basis and suitable functional from the complete-intersection hypotheses remains to prove.",
        "在局部底环 B 上，给定 A 的有限 B-基及 B-线性泛函 ℓ，若 Gram 行列式在 B/m_B 中非零，Lean 构造以 ℓ 为泛函的完美乘法配对。从完全交假设得到相应基与泛函的步骤仍待证明。"
      ]
    ],
    "formulas": [
      "G_{\\ell,ij}=\\ell(b_jb_i)",
      "\\det G_{\\ell}\\notin\\mathfrak m_B\\Rightarrow\\det G_{\\ell}\\in B^{\\times}"
    ],
    "proof": [
      [
        "Local-ring criterion",
        "局部环判据",
        "A determinant not in the maximal ideal is a unit.",
        "不属于极大理想的行列式是单位。"
      ],
      [
        "Build the inverse",
        "构造逆映射",
        "Use the actual Gram matrix inverse and the dual basis to construct the linear equivalence Ψ(x)(a)=ℓ(xa). The structure is constructed; no perfect-pairing structure is an input.",
        "使用真正的 Gram 矩阵逆及对偶基构造线性同构 Ψ(x)(a)=ℓ(xa)；不再输入现成的完美配对结构。"
      ]
    ]
  },
  {
    "id": "generic",
    "title": [
      "Descend from the generic fiber",
      "从泛纤维下降"
    ],
    "summary": [
      "Flatness proves injectivity at the base nonzerodivisors.",
      "平坦性保证沿底环非零因子局部化的单射性。"
    ],
    "formula": "N_K\\Delta_K=0\\Rightarrow N\\Delta=0",
    "file": "Linear/GenericFiber.lean",
    "decl": "flat_genericFiber_descend_annihilation",
    "scope": "conditional",
    "deps": [
      "jacobian"
    ],
    "statement": [
      [
        "Let A be a flat B-algebra and f:A→C a localization at the nonzerodivisors of B. Lean proves f is injective. If the image ideal of N annihilates f(δ), then N annihilates δ in A. The localized SS identity is still an explicit input.",
        "设 A 为平坦 B-代数，f:A→C 为沿 B 的非零因子的局部化。Lean 证明 f 单射；若 N 的像理想湮灭 f(δ)，则 N 在 A 中湮灭 δ。局部化后的 SS 恒等式仍是显式输入。"
      ]
    ],
    "formulas": [
      "A\\hookrightarrow S^{-1}A,\\qquad S=B\\setminus\\{\\text{zero divisors}\\}",
      "f(n\\delta)=f(n)f(\\delta)=0\\Rightarrow n\\delta=0"
    ],
    "proof": [
      [
        "Flatness",
        "平坦性",
        "A base nonzerodivisor acts injectively on a flat module. The localization equality criterion gives injectivity of f.",
        "底环非零因子在平坦模上作用单射；局部化相等判据给出 f 的单射性。"
      ],
      [
        "Descent",
        "下降",
        "For every n∈N, the localized annihilation identity kills f(nδ). Injectivity then kills nδ.",
        "对任意 n∈N，局部化后的湮灭关系令 f(nδ)=0，单射性推出 nδ=0。"
      ]
    ]
  },
  {
    "id": "target",
    "title": [
      "Relative Jacobian lemma",
      "相对 Jacobian 引理"
    ],
    "summary": [
      "Full Lemma 3.1. Its formal proof remains open.",
      "完整引理 3.1；其形式化证明尚未完成。"
    ],
    "formula": "\\operatorname{Ann}_A(N)=B\\Delta",
    "deps": [
      "primitive",
      "parameters",
      "quotient"
    ],
    "x": 665,
    "y": 250,
    "file": "Linear/Target.lean",
    "scope": "pending",
    "goal": true,
    "statement": [
      [
        "Let B=ℂ[[s₁,…,sᵣ]], R=B[[z₁,…,z꜀]], and A=R/(H₁,…,H꜀), with r,c≥1 and H a regular sequence. Assume A is finite flat over B and A_red≅B as a B-algebra. Put N=√0 and Δ=det(∂Hᵢ/∂zⱼ) in A.",
        "设 B=ℂ[[s₁,…,sᵣ]]，R=B[[z₁,…,z꜀]]，A=R/(H₁,…,H꜀)，其中 r,c≥1，H 为正则序列。假设 A 在 B 上有限平坦，且 A_red≅B 为 B-代数同构。记 N=√0，Δ=det(∂Hᵢ/∂zⱼ)∈A。"
      ],
      [
        "(1) Ann_A(N)=BΔ. (2) If τ₁,…,τᵣ reduce to a regular parameter system of A/N, then the image of Δ in Q=A/(τ₁,…,τᵣ) is nonzero and generates Soc(Q).",
        "(1) Ann_A(N)=BΔ。(2) 若 τ₁,…,τᵣ 约化后为 A/N 的正则参数系，则 Δ 在 Q=A/(τ₁,…,τᵣ) 中的像非零并生成 Soc(Q)。"
      ]
    ],
    "formulas": [
      "\\operatorname{Ann}_A(N)=B\\Delta",
      "\\operatorname{Soc}\\bigl(A/(\\tau_1,\\ldots,\\tau_r)\\bigr)=\\mathbb C\\overline\\Delta,\\qquad\\overline\\Delta\\ne0"
    ],
    "proof": [
      [
        "What is already checked",
        "已验证范围",
        "Read the green and conditional cards for exact Lean theorem types. The full target is a defined Prop, not a proved theorem.",
        "绿色及条件式卡片给出精确 Lean 定理类型。完整目标目前是已定义的 Prop，并非已证明定理。"
      ],
      [
        "What remains",
        "待完成内容",
        "Construct complete-intersection duality; formalize the SS Jacobian theorem and its family compatibility; construct arbitrary parameter lifts and prove their quotient socle conclusion.",
        "构造完全交对偶；形式化 SS Jacobian 定理及其族兼容性；构造任意参数提升并证明商环的 socle 结论。"
      ]
    ]
  }
];
