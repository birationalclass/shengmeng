export const language=new URLSearchParams(location.search).get('lang')||localStorage.getItem('formalization-language')||'zh';
export const english=language==='en';
export const englishStatuses={done:'✓ Verified by Lean',conditional:'◐ Conditional proof · inputs open',assumption:'? Assumed input',pending:'○ Open geometric goal'};
// Node translations preserve the distinction between model proofs and geometric inputs.
const entries={
dvrfoundation:['Normal one-dimensional local ring ⇒ DVR','A Noetherian integrally closed local domain of Krull dimension one is a DVR; this is connected to actual integral Scheme stalks.','Reuses the verified mathlib DVR characterization. DVR is not assumed here. Identifying geometric codimension one with stalk dimension one remains open.',['Noetherian integrally closed local domain.','ringKrullDim R = 1.'],[['Exclude fields','A field has Krull dimension zero.'],['Nonzero primes','Dimension at most one makes each nonzero prime the maximal ideal.'],['DVR characterization','Integral closure and the prime condition give a PID; excluding fields gives a DVR.']]],
valuative:['Proper valuative criterion: DVR lift','A DVR/fraction-field square over an actual proper Scheme morphism has a unique lift.','Reuses mathlib’s proved proper/separated valuative criteria. Birational generic maps and the commuting square must still be constructed; existence of the lift is not assumed.',['An actual Scheme morphism f with IsProper f.','DVR R, fraction field K and a commuting square.'],[['Proper criterion','Obtain ValuativeCriterion f from IsProper f.'],['Lift existence','Extract a lift and both commuting triangles.'],['Uniqueness','Proper implies separated, giving the unique lift.']]],
zmtfinite:['mathlib: Zariski main corollaries','Proper + quasi-finite implies finite; a finite fiber of a proper morphism has a neighborhood on which the morphism is finite.','Integration of existing mathlib results, compiled with our pinned version. Finite birational isomorphisms over normal bases and contracted-curve existence are not yet proved here.',['IsProper f; the first result also requires LocallyQuasiFinite f.','The neighborhood result assumes (f⁻¹{y}).Finite.'],[['Existing theorem','Use IsFinite.of_isProper_of_locallyQuasiFinite.'],['Finite-fiber neighborhood','Use exists_isFinite_morphismRestrict_of_finite_preimage_singleton.'],['Remaining geometry','Connect finite birationality and normality to isomorphisms, then positive-dimensional fibers to curves.']]],

localorder:["Local DVR coefficients and isomorphisms", "DVR isomorphisms preserve orders; actual Scheme stalk isomorphisms preserve fraction orders and force residue degree one.", "Local algebra and actual stalk/residue-field APIs are verified. Proper birationality and normality have not yet been connected to codimension-one stalk isomorphisms.", ["Specified DVR local rings and ring isomorphisms.", "Nonzero numerators and denominators.", "IsIso for the actual Scheme stalk map."], [["Preserve orders", "A nonzero element is a unit times a uniformizer power; an isomorphism preserves the exponent."], ["Fraction orders", "ord(a/b)=ord(a)−ord(b); cross multiplication proves independence of representation."], ["Actual stalks", "Apply the local calculation to Scheme.stalkMap when it is an isomorphism."], ["Degree one", "A stalk isomorphism induces a residue-field isomorphism, so residueDegree=1."]]],
codimone:["Codimension-one isomorphism over a normal base", "Construct an isomorphism open containing every codimension-one point from proper birationality and normality.", "This geometric existence result remains open in Lean. It is not an effectivity-preservation assumption. Standard reference: Stacks 0BFP.", ["Codimension-one local rings of the normal Noetherian base are DVRs.", "Proper birational morphisms are isomorphisms near these points.", "Construct strict transforms and actual stalk isomorphisms."], [["Normal local rings", "A normal codimension-one local ring is a DVR."], ["Proper birationality", "Use the DVR argument to obtain an isomorphism near the point."], ["Strict transforms", "Use the unique corresponding point on the isomorphism open."]]],
localcartier:["Cartier local equations and Weil cycles", "Construct actual Cartier pullback and its underlying Weil cycle from rational local equations, with DVR orders as coefficients.", "Representation independence and invariance under local isomorphisms are proved. Gluing, actual Cartier pullback and local finiteness still require construction.", ["Actual Cartier local equations and unit transition data.", "Pullback of rational functions along π.", "Orders define a Weil cycle with locally finite support."], [["Cartier data", "Glue local rational equations modulo units and define actual pullback."], ["Weil cycle", "Take DVR orders at codimension-one points and prove local finiteness."], ["Strict-transform coefficients", "Use the proved order invariance to recover coefficients."]]],
pushpullcriterion:["Local criterion for actual cycle push-pull", "Matching strict-transform coefficients, actual stalk isomorphisms and weight drop on other components imply actual cycle pushforward equals D.", "Proves AlgebraicCycle.map π wx wy lifted=D without assuming hleft. Constructing strict transforms, stalk isomorphisms and actual Cartier coefficients from geometry remains open.", ["hcoeff: lifted(strict y)=D(y).", "hsection: π(strict y)=y whenever D(y) is nonzero.", "hweight: equal weights on nonexceptional components.", "hstalk: IsIso for their actual stalkMap.", "hexceptional: other components have coefficient zero or dimension/weight drop."], [["Exceptional contributions", "Weight drop makes mapCoeff zero."], ["Strict-transform degree", "An actual stalk isomorphism gives residueDegree=1."], ["Recover coefficients", "Each downstairs coefficient has a single surviving strict-transform contribution, equal to D(y)."], ["Cycle equality", "Pointwise ext yields π_*lifted=D."]]],

pushpull:["Actual divisor push-pull identity", "For proper birational π between normal varieties and an R-Cartier divisor D, prove π_*(π*D)=D.", "The actual cycle coefficient argument is verified. Constructing the codimension-one isomorphism open from normal proper birational geometry, and actual Cartier pullback/Weil-cycle data, remains open.", ["Use actual Cartier pullback, not an arbitrary effective lift.", "Strict-transform coefficients and residue degrees recover D.", "Exceptional components have zero pushforward by dimension drop."], [["Strict transforms", "Each base prime divisor recovers its coefficient on the nonexceptional strict transform."], ["Exceptional components", "Dimension-dropping components push to zero."], ["Cycle equality", "Compare all prime-divisor coefficients to prove π_*(π*D)=D."]]],
projectioncases:["Projection cases from cycle pushforward", "Given intersection/pushforward compatibility, derive zero intersection on contracted components and residue-degree multiples on equal-weight components.", "The two cases are derived using actual AlgebraicCycle.map. The zero/multiple disjunction is no longer an independent input; hcompat still is.", ["Additive cycle-intersection maps up and down.", "hcompat: up([Γ])=down(π_*[Γ]).", "Weights encode actual dimensions of curves and their images."], [["Push the cycle", "Use the actual single-component pushforward formula."], ["Additive intersection", "An additive map sends natural multiples of cycles to multiples of intersection numbers."], ["Split the cases", "Weight drop gives zero; equal weight gives residueDegree times the image intersection."]]],
realspan:["Real linear extension of projection", "Agreement on Cartier generators implies agreement on their real span.", "The real-linear step is verified. Actual Cartier generators, pullback and intersection maps still require geometric construction.", ["Real-linear pullback and intersection maps.", "D lies in the real span of Cartier generators.", "Projection identity on Cartier generators."], [["Compare linear maps", "Regard both sides as real-linear maps to real numbers."], ["Check generators", "Equality on Cartier generators is an explicit input."], ["Extend", "LinearMap.eqOn_span proves equality on every finite real-linear combination."]]],
max:['Finite coefficients · maximum ratio','There exists e > 0 such that d+e·a is nonnegative and vanishes at an originally negative coefficient.','Fully verified for finitely supported real coefficients.',['a is nonnegative.','a is strictly positive wherever d is negative.'],[['Finite negative support','Filter the finite support of d by negative coefficients.'],['Maximum ratio','Take the maximum of −dᵢ/aᵢ over this nonempty finite set.'],['Nonnegativity','Use the maximum bound on negative entries and positivity on the remaining entries.'],['A vanishing entry','At a maximizing index, dⱼ+e·aⱼ=0.']]],
least:['Least effective shift','For t ≥ 0, d+t·a is effective exactly when e ≤ t.','A verified threshold characterization in the coefficient model.',['The same coefficient hypotheses as the maximum-ratio lemma.'],[['Reuse the maximum','Obtain e and a vanishing index.'],['Necessity','The vanishing entry implies e ≤ t.'],['Sufficiency','Nonnegative coefficients make every larger shift effective.']]],
push:['Effectivity under coefficient pushforward','Reading coefficients along an injective strict-transform map preserves nonnegativity.','Verified for finite coefficient vectors; the geometric cycle correspondence remains open.',['An injective map strict : J → I.','Effective input coefficients.'],[['Define pushforward','Read coefficients at strict(j) using Finsupp.comapDomain.'],['Check each entry','Nonnegativity follows directly at strict(j).']]],
negative:['Negative coefficients are exceptional','If the coefficient pushforward is effective, every negative index lies outside the strict-transform image.','ExceptionalIndex means outside the image; identifying it with geometric exceptional divisors remains open.',['Effective coefficient pushforward.','A negative coefficient.'],[['Suppose it is in the image','Write i=strict(j).'],['Contradiction','The pushed coefficient is simultaneously nonnegative and negative.']]],
antiample:['Existence of E','Construct an effective Cartier divisor E with −E relatively ample over an affine base.','The sheaf, section and relative-ampleness construction is still a geometric input.',['A relatively ample Cartier divisor and a nonzero section of its negative.','The current conditional theorem takes E as a parameter.'],[['Choose an ample divisor','Choose an f-ample Cartier divisor A.'],['Find a section','The rank-one direct image on the affine base has a nonzero section s.'],['Define E','Set E=−A+div(s); then E is effective and −E is relatively ample.']]],
strict:['Strict transforms and cycle pushforward','Identify the coefficient model with strict transforms, exceptional divisors and actual cycle pushforward.','This geometric correspondence has not been proved.',['Codimension-one properties of normal birational morphisms.','Agreement of cycle pushforward with strict-transform coefficients.'],[['Strict transforms','Construct the unique nonexceptional strict transform of each base prime divisor.'],['Check coefficients','Verify degrees and dimension conditions for cycle pushforward.']]],
cover:['Curves covering exceptional points','Each exceptional point lies on a complete contracted curve.','The normal-base isomorphism criterion and projective-fiber curve existence remain inputs.',['Zariski’s main theorem and proper quasi-finite ⇒ finite are proved in mathlib; the finite-birational isomorphism corollary over a normal base still needs connecting.','Curves through specified points in positive-dimensional projective fibers.'],[['Find positive-dimensional fibers','Use the normal-base birational isomorphism criterion.'],['Choose a curve','Take a contracted curve through the chosen point.']]],
intersection:['Geometric intersection and positivity','Construct D·C and prove the signs supplied by nefness, ampleness and effectivity.','The current intersection functional is a parameter, not a constructed geometric degree.',['−D nef gives D·C ≤ 0; −E ample gives E·C < 0.','Effective divisors have nonnegative degree off their support, strictly positive if they meet the curve.'],[['Define degree','Construct intersection with Cartier and real Cartier divisors.'],['Prove signs','Connect positivity and support conditions with the required inequalities.']]],
curves:['A curve in the vanishing component','A vanishing exceptional component supplies a contracted curve outside the shifted support.','Curve existence and its nonnegative intersection are separate explicit inputs.',['Geometric support and curve-existence properties.'],[['Choose a point','Choose x in F outside the support.'],['Choose a curve','Take a contracted curve through x in F.']]],
connected:['Connected fibers and crossing curves','Partial intersection with the support supplies a fiber curve meeting but not contained in it.','Topological connectedness alone is insufficient; the projective geometry remains open.',['Connected fibers from Stein factorization.','The appropriate curve-existence lemma in projective fibers.'],[['Connectedness','Establish geometric connectedness of the fibers.'],['Crossing curve','Find a suitable component and choose a curve inside it.']]],
support:['Conditional support containment','Curve coverage and degree signs imply exc ⊆ supp.','Verified set and inequality reasoning; coverage and degree signs are parameters.',['Each exceptional point lies on a test curve.','Test curves have negative degree.','Curves outside the support have nonnegative degree.'],[['Choose a curve','Use the coverage hypothesis at each exceptional point.'],['Force containment','Otherwise its degree is both nonnegative and negative.'],['Return to the point','The point belongs to the curve and thus to the support.']]],
core:['Numerical negativity core','Given the coefficient and intersection conditions for E, all coefficients of D are nonnegative.','Curves, linear maps and sign conditions are explicit theorem parameters.',['E is effective and covers the negative coefficients.','Nef and anti-ample degree signs.','A curve test at a vanishing component.'],[['Assume a negative coefficient','Use the maximum-ratio shift.'],['Test the effective shift','Obtain a curve with nonnegative intersection with D+eE.'],['Contradiction by linearity','Expand the degree; nefness and e>0 make it strictly negative.']]],
iff:['Effective iff pushforward effective','Under the strict-transform model and curve interfaces, effectivity is equivalent to effective pushforward.','A verified conditional result; the full scheme-theoretic theorem remains open.',['Injective strict transforms and linear coefficient/intersection maps.','E, coverage, nefness and anti-ampleness hypotheses.','Curve existence and nonnegative intersection off support.'],[['Forward direction','Coefficient pushforward preserves effectivity.'],['Negative entries are exceptional','Effective pushforward excludes negative strict-transform coefficients.'],['Apply the core','Combine curve existence and nonnegative intersection with the numerical theorem.']]],
projective:['Geometric projective version (1)','For a projective birational morphism of normal varieties and −D relatively nef, D ≥ 0 iff f∗D ≥ 0.','The full geometric statement is not yet a Lean theorem in this project.',['Instantiate all interfaces with actual algebraic-geometric objects.'],[['Construct geometric objects','Connect Cartier divisors, cycle coefficients and intersection.'],['Prove geometric inputs','Prove the strict-transform, E, curve and degree properties.'],['Apply the conditional theorem','Instantiate effective_iff_push_effective.']]],
fiber:['Conditional fiber-support dichotomy','A fiber is disjoint from the support or contained in it.','The set-theoretic contradiction is verified; curve existence and strict positivity are inputs.',['A suitable curve if the fiber partly meets the support.','Strict positive degree when meeting but not contained.','Nonpositive degree on fiber curves.'],[['Split by intersection','The disjoint case is immediate.'],['Assume noncontainment','Use the curve-existence hypothesis.'],['Contradiction','The same curve has both positive and nonpositive degree.']]],
projective2:['Separate conclusion: fiber support (1.4(2))','Let f:X→Y be projective birational between normal varieties. If D is an effective R-Cartier divisor and −D is f-nef, every fiber is disjoint from Supp D or contained in it.','This is the separate conclusion of Theorem 1.4(2). It is not used in the effectivity proof of (1); fiberdown only descends it to proper version (2). Effectivity alone is insufficient.',['f is projective birational between normal varieties.','D is effective R-Cartier and −D is f-nef.','Actual connected fibers, fiber curves and intersection must instantiate the interfaces.'],[['Assume the fiber meets support','If it is not contained, choose a fiber curve meeting but not contained in the support.'],['Contradict nefness','D·C>0, while −D being f-nef gives D·C≤0; hence the fiber is contained in support.'],['Separate use','Descend proper version (2); the effectivity proof of (1) does not use this result.']]],
chow:['Chow modification and geometric identities','Remaining inputs: a normal Chow modification and actual projection, push-pull and support identities.','The logical and set-theoretic descent steps have been separated and verified.',['A normal modification making the composite projective.','Actual push-pull and projection formulas.','Surjectivity and equality of pulled-back supports.'],[['Modify','Construct π making f∘π projective.'],['Geometric identities','Prove the actual divisor and intersection formulas.'],['Use verified descent','Apply the separate descent theorems.']]],
proper:['Proper negativity lemma','For proper birational f between normal varieties and R-Cartier D with −D f-nef: (1) effectivity iff effective pushforward; (2) the fiber-support alternative when D is effective.','Two separate branches: properreduce handles (1), fiberdown handles (2). The latter is not a premise of the effectivity proof. Full geometric proofs remain open.',['The projective geometric versions and the Chow identities.'],[['Projective versions','Complete effectivity and support statements.'],['Modification','Lift the proper problem to a projective model.'],['Descent','Apply the verified reduction and support descent.']]],
coefflaws:['Coefficient composition and kernel','Pushforward composes; zero pushforward characterizes exceptional support; exceptional terms leave pushforward unchanged.','Six coefficient-model results are verified. The embedding section is not geometric Cartier pullback.',['Injective strict-transform maps.','Finitely supported coefficients.'],[['Composition and kernel','Read coefficients to prove both identities.'],['Section and exceptional terms','Pushing embedded coefficients restores them; exceptional terms push to zero.'],['Effectivity descent','Reuse the verified effectivity-preserving pushforward.']]],
projection:['Geometric projection formula','Prove (π*D)·Γ = D·π_*[Γ], then deduce relative nefness of −π*D.','The geometric intersection identity remains open. Actual scheme-cycle pushforward properties and the nef-sign consequence are verified.',['π:X′→X is proper birational, f:X→Y, g=f∘π; D is R-Cartier on X.','Γ⊂X′ is a proper integral curve contracted by g.','Construct actual Cartier pullback and intersection and prove the projection identity.'],[['Contracted by π','The cycle pushforward is zero; prove (π*D)·Γ=0.'],['Curve image','For C=π(Γ), let r=[k(Γ):k(C)]>0; prove (π*D)·Γ=r(D·C).'],['Nef pullback','f contracts C, so D·C≤0 implies nonpositive pullback degree.']]],
geomcycle:["Actual scheme-cycle pushforward", "For actual Scheme cycles, prove effectivity preservation and single-component zero / degree-multiple pushforward.", "These results use the actual Scheme-cycle API. Weights still need geometric dimension choices; Cartier intersection compatibility is not included.", ["A quasi-compact scheme morphism.", "Weight functions specifying dimension or codimension.", "Real coefficients with pointwise effectivity."], [["Effectivity", "Each term has a nonnegative coefficient and natural multiplicity."], ["Weight drop", "The entire single-component cycle pushes to zero."], ["Equal weight", "The single-component cycle pushes to residueDegree times the image cycle."]]],
nefpull:["Nef signs under actual cycle pushforward", "Actual cycle pushforward and intersection compatibility preserve nonpositive pullback intersections.", "Verified conditionally on the actual Scheme-cycle API. The old disjunction is replaced by the proved cycle cases; intersection compatibility and admissible image curves remain explicit.", ["hcompat: upstairs intersection equals downstairs intersection against the pushed cycle.", "Equal-weight images are admissible contracted test curves downstairs.", "Downstairs test-curve intersections are nonpositive."], [["Use cycle cases", "Derive zero or residue-degree multiple from actual cycle pushforward."], ["Preserve signs", "Natural degree weights are nonnegative, so nonpositive intersections remain nonpositive."]]],
effdown:["Effectivity descent via pushforward", "Actual Scheme-cycle pushforward preserves effectivity. If π_*(π*D)=D and π*D is effective, then D is effective.", "Descent now uses actual AlgebraicCycle.map. The remaining geometric map-property input is hleft for actual Cartier pullback; hlifted is the condition known when applying descent.", ["hleft: AlgebraicCycle.map π wx wy lifted = D; lifted is the underlying cycle of actual π*D.", "hlifted: CycleEffective lifted, the effective pullback obtained upstairs.", "Effectivity-preserving pushforward is proved by scheme_cycle_map_effective, not assumed."], [["Use proved effectivity preservation", "Push effective lifted through actual AlgebraicCycle.map."], ["Substitute the missing identity", "hleft identifies the effective pushforward with D."]]],
setdown:['Set descent under surjections','Surjective preimages reflect containment and disjointness, so the support dichotomy descends.','Fully verified set-theoretic reasoning with no additional geometry.',['A surjective map.'],[['Take preimages of points','Surjectivity reflects each set relation.'],['Descend the alternatives','Handle disjointness and containment separately.']]],
properreduce:['Proper-to-projective reduction','The projective negativity implication yields the proper effectivity equivalence under modification identities.','The reduction logic is verified. Chow existence, geometric formulas and the geometric projective theorem remain inputs.',['Push-pull and commuting pushforward identities.','Nef pullback and the projective negativity implication.'],[['Lift','Transport nefness and effective base pushforward.'],['Projective implication','Apply negativity upstairs.'],['Descend','Push back to prove D effective.']]],
fiberdown:['Fiber-support descent','The support alternative on every composite fiber descends through a surjective modification.','Fiber and set reasoning is verified; geometric support pullback and the projective fiber theorem remain inputs.',['A surjective modification.','The upstairs support is the preimage of the downstairs support.','The support alternative for all upstairs fibers.'],[['Composite fibers','A composite fiber is the preimage of an original fiber.'],['Surjective descent','Apply the verified set dichotomy descent.']]]
};
Object.assign(entries,{
affinesections:['Nonzero sections of affine quasicoherent sheaves','A nonzero quasicoherent O-module on an actual Spec R has a nonzero global section.','Proved using the affine sheaf–module equivalence. Quasicoherence and nonzeroness of the specific direct image f_*O_X(−A) still need proving.',['An actual quasicoherent O-module M on Spec R.','M is nonzero (¬ IsZero M).'],[['Assume all sections vanish','The global-section module is a zero object.'],['Affine equivalence','M is isomorphic to the tilde sheaf of its global-section module, so M is zero too.'],['Contradiction','Nonzeroness gives a nonzero global section.']]],
normalfinite:['Affine finite birational isomorphism over a normal base','If R is an integrally closed domain and S is a finite R-algebra embedded in Frac(R), Spec S→Spec R is an isomorphism.','Both the ring-map bijectivity and IsIso of the actual Spec map are proved. Constructing this affine data from general Scheme birationality and gluing remain open.',['R is an integrally closed domain and K is its fraction field.','S is finite as an R-module.','An injective R-algebra map j:S→K supplies the birational algebraic data.'],[['Finite implies integral','Every element of S is integral over R.'],['Integral closure','Its image in Frac(R) belongs to R.'],['Recover the element','Injectivity of j gives surjectivity of R→S; the fraction-field map gives injectivity.'],['Actual Scheme isomorphism','Apply the contravariant Spec functor to the ring isomorphism.']]],
antiample:['Existence of E','Construct an effective Cartier divisor E with −E relatively ample over an affine base.','Choose i*O(1) from the projective embedding by definition. The affine nonzero-section theorem is proved. The O(1)/direct-image interfaces and the effective Cartier zero divisor still need construction.',['Choose a projective closed embedding i:X→P^n_R and L=i*O(1)≅O_X(A). No deep existence theorem for A is needed.','Prove F=f_*L⁻¹ quasicoherent and nonzero, then apply affinesections.','Construct E=−A+div(s), prove effectivity and O_X(−E)≅L.'],[['Choose A from the embedding','L=i*O(1) is f-very ample, hence f-ample. These geometric interfaces still need implementation.'],['Nonzero direct image','F is invertible over the dense birational isomorphism open, so nonzero; quasicoherence also needs proving.'],['Affine nonzero section: verified','Apply affine_quasicoherent_exists_nonzero_section to the nonzero quasicoherent F.'],['Section to divisor','Construct effective Cartier E=−A+div(s) and prove O_X(−E)≅L. This geometric bridge remains open.']]]
});
entries.cover[3]=['Proper quasi-finite implies finite is integrated. The normal-base finite birational isomorphism is proved for affine rings and actual Spec maps; general Scheme affine reduction and gluing remain open.','Curves through specified points in positive-dimensional projective fibers.'];
Object.assign(entries,{
  "curvefiberdegree": [
    "Local degree for finite flat curves",
    "Actual finite flat algebras satisfy Σ e_q f_q=[L:K] on each prime fiber, for the corresponding fraction fields.",
    "Uses actual ramification indices, residue degrees and function fields. The intersection projection identity is not assumed.",
    [
      "A finite flat algebra over a domain; p is prime and its prime fiber has a Fintype instance.",
      "Compatible fraction fields K and L."
    ],
    [
      [
        "Fiber length",
        "Use the verified Σ e_q f_q=rank_R S."
      ],
      [
        "Function-field degree",
        "The fraction-field dimension equals the module rank."
      ],
      [
        "Signed multiplicity",
        "For any integer n, the contribution is n·[L:K]."
      ]
    ]
  ],
  "curveorder": [
    "Pullback of local-equation orders",
    "On actual Dedekind rings and fraction fields, ord_q(h*a)=e_q ord_p(a); orders add on products.",
    "Defined from normalized adic valuations and proved from mathlib. This concerns local equations on affine normal curves, not a supplied Cartier compatibility law.",
    [
      "Dedekind domains R and S; S is torsion-free over R.",
      "Actual height-one primes q over p and a nonzero rational function a."
    ],
    [
      [
        "Actual valuation",
        "ord_p(a)=−log(v_p(a))."
      ],
      [
        "Pull back the valuation",
        "v_q(h*a)=v_p(a)^e_q."
      ],
      [
        "Take logarithms",
        "Deduce ord_q(h*a)=e_q ord_p(a)."
      ]
    ]
  ],
  "localprojection": [
    "Local projection: orders and residue degrees",
    "For finite flat affine Dedekind curves, Σ ord_q(h*a) f_q=ord_p(a)[L:K].",
    "Actual orders, ramification indices and residue degrees are used. Gluing on complete curves is still required for the global line-bundle degree formula.",
    [
      "A finite flat Dedekind-domain extension with compatible fraction fields K→L.",
      "An actual nonzero prime p, a∈Kˣ, and a finitely enumerable prime fiber."
    ],
    [
      [
        "Construct fiber points",
        "Lying-over primes are nonzero and therefore actual height-one points."
      ],
      [
        "Substitute orders",
        "Replace ord_q(h*a) by e_q ord_p(a)."
      ],
      [
        "Sum the contributions",
        "Use Σ e_q f_q=[L:K]."
      ]
    ]
  ],
  "principaldivisor": [
    "Principal Weil divisors on affine curves",
    "An actual rational function gives a finitely supported principal Weil divisor. It is effective iff the function belongs to the coordinate ring, and zero iff the function is a coordinate-ring unit.",
    "Actual Dedekind coordinate rings and valuations. Finite support and invariance under unit transitions are proved; global Cartier gluing and degree on complete curves remain open.",
    [
      "An actual Dedekind domain R and its fraction field K.",
      "A nonzero rational function a∈Kˣ."
    ],
    [
      [
        "Finite support",
        "Nonzero orders lie in the finite pole sets of a or a⁻¹."
      ],
      [
        "Construct the divisor",
        "Build Finsupp with coefficients ord_p(a)."
      ],
      [
        "Unit transitions",
        "A regular unit changes no coefficient; products add divisors and inversion negates them."
      ],
      [
        "Effectivity and zero",
        "No poles gives a∈R; regularity of both a and a⁻¹ gives a unit."
      ]
    ]
  ],
  "pullbackdiagram": [
    "Pullback around the curve square",
    "For the actual commuting Scheme square Γ→X′ and C→X, i*π*L≅h*j*L.",
    "Uses actual Scheme module-sheaf pullback composition and congruence. Only square commutativity is assumed, not the intersection projection formula. Global degree is a separate step.",
    [
      "Actual Schemes and morphisms i,π,h,j with i≫π=h≫j.",
      "Any actual module sheaf L downstairs; apply to 𝒪_X(D)."
    ],
    [
      [
        "Compose pullbacks",
        "i*π*L≅(π∘i)*L."
      ],
      [
        "Use the square",
        "π∘i=j∘h."
      ],
      [
        "Decompose the other path",
        "(j∘h)*L≅h*j*L; compose the isomorphisms."
      ]
    ]
  ],
  "projection": [
    "Geometric curve projection formula",
    "Prove (π*D)·Γ=D·π_*[Γ] by restricting to the curve and taking degree.",
    "The actual module-sheaf pullback square, affine Dedekind order pullback and local degree are verified. Constructing degree on complete curves, gluing, normalization and actual Cartier intersection remain open.",
    [
      "Verified: i*π*L≅h*j*L, ord_q(h*a)=e_q ord_p(a), and Σe_qf_q=[k(Γ):k(C)].",
      "Open: construct line-bundle degree on complete integral curves and prove deg(h*L)=[k(Γ):k(C)]deg(L), including normalization and the point-image case.",
      "Instantiate the degree formula as Cartier intersection, then use the verified real-span extension."
    ],
    [
      [
        "Restrict to the curve: pullback verified",
        "Use the commuting square Γ→X′, C→X to obtain i*π*𝒪(D)≅h*j*𝒪(D)."
      ],
      [
        "Local orders and degree: verified",
        "On affine normal curves, orders pull back with ramification index; residue-degree-weighted fiber contributions multiply by the function-field degree."
      ],
      [
        "Complete-curve degree: open",
        "Glue local equations, prove the line-bundle degree formula, and handle normalization and point images."
      ],
      [
        "Return to intersection",
        "With L=j*𝒪(D), (π*D)·Γ=deg(h*L)=r deg L=D·π_*[Γ]; extend by real linearity."
      ]
    ]
  ]
});
Object.assign(entries,{
  "pointtensor": [
    "Tensor pullback and multiplicity of a point divisor",
    "The actual tensor pullback of p has finite local length m_q at q; Σm_q[k(q):k]=[L:K][k(p):k].",
    "The affine local algebra of the proposed point-counting route is verified: tensor quotient, finite length, ramification multiplicity and base-field weights. Divisor representation of general line bundles, complete-curve gluing and normalization remain open.",
    [
      "Finite-type Dedekind coordinate rings over k; a finite flat R-algebra S.",
      "Actual nonzero prime p and primes q over it.",
      "Compatible fraction fields K,L and a finitely enumerable prime fiber."
    ],
    [
      [
        "Tensor pullback of a point",
        "S_q/𝔪_pS_q ≅ S_q⊗_R(R/𝔪_p)."
      ],
      [
        "Multiplicity",
        "Quasi-finiteness and Noetherianness give finite length m_q=e_q."
      ],
      [
        "Count with multiplicity",
        "Σm_q[k(q):k(p)]=[L:K]."
      ],
      [
        "Base-field point degree",
        "The residue-degree tower gives Σm_q[k(q):k]=[L:K][k(p):k]."
      ]
    ]
  ],
  "closedpoint": [
    "A closed point outside the shifted support",
    "In an actual scheme of finite type over a field, closed F not contained in closed Z contains a closed point outside Z.",
    "Derived from mathlib Jacobsonness, not a point-existence hypothesis. Applying it still needs the actual Weil-support interpretation of the zero coefficient; a contracted curve through the point remains to be constructed.",
    [
      "An actual scheme locally of finite type over a field.",
      "Closed subsets F,Z with F not contained in Z."
    ],
    [
      [
        "Nonempty complement",
        "F not contained in Z gives a point of F∖Z."
      ],
      [
        "Locally closed",
        "F∖Z is locally closed."
      ],
      [
        "Jacobsonness",
        "A nonempty locally closed subset has a closed point."
      ]
    ]
  ],
  "localidempotents": [
    "Local-ring idempotents and product decompositions",
    "An actual local ring has only idempotents 0 and 1, and cannot be a product of two nonzero rings.",
    "The last algebraic contradiction in the Hartshorne III §11 formal-functions argument is verified. Creating a nontrivial completed-ring idempotent from a disconnected geometric fiber remains open.",
    [
      "An actual commutative local ring R.",
      "a²=a; or an isomorphism R≅A×B with both factors nonzero."
    ],
    [
      [
        "A unit alternative",
        "At least one of a and 1−a is a unit."
      ],
      [
        "Cancel the unit",
        "Idempotency forces a=1 or a=0."
      ],
      [
        "Exclude a product",
        "(1,0) is a nontrivial idempotent in a product of nonzero rings."
      ]
    ]
  ],
  "curves": [
    "A contracted curve in the zero-coefficient component",
    "The construction of e gives a negative exceptional component F with coefficient zero in D+eE. Choose a closed point outside the shifted support, then a contracted curve in F through it.",
    "The maximum-ratio and zero-coefficient steps, and closed-point selection in finite-type schemes, are verified. F is not a support component; it need not be disjoint from the support. Actual Weil support and the curve inside F remain geometric bridges. This branch does not use fiber connectedness.",
    [
      "D is not effective but f_*D is effective, so negative components are exceptional.",
      "Effective E contains the exceptional locus, so its coefficients on those components are positive.",
      "The maximum-ratio step gives coeff_F(D+eE)=0; actual support semantics gives F not contained in Supp(D+eE).",
      "A closed point can be selected; construct a complete curve through it in a positive-dimensional fiber of f|F."
    ],
    [
      [
        "Get the zero component",
        "The maximum ratio gives an effective D+eE and a zero coefficient on a negative component F."
      ],
      [
        "Closed point: verified",
        "F is not a support component. Apply the finite-type closed-point lemma outside that support."
      ],
      [
        "Curve inside F: geometric bridge",
        "Construct a complete curve C⊂F through the point in a fiber of f|F. The point is outside the support, so C is not contained in it."
      ]
    ]
  ],
  "connected": [
    "Connected fibers and crossing curves (part 2)",
    "The independent part (2) route: a connected fiber partially meeting support must supply a curve meeting but not contained in it; the higher-dimensional selection argument needs repair.",
    "Only used by the fiber-support alternative, not by part (1) or proper effectivity descent. Follow Hartshorne III §11 via normality, formal functions and idempotents; the final local-ring contradiction is verified. Contracted-curve coverage alone does not imply the required crossing condition.",
    [
      "First prove f_*𝒪_X=𝒪_Y using birational fraction-field embedding, proper direct-image finiteness and integral closure.",
      "Formal functions: Â≅lim H⁰(X_n,𝒪_Xn); disconnectedness gives compatible nontrivial idempotents. This geometric bridge remains open.",
      "The local-ring contradiction is verified, but does not itself establish fiber connectedness.",
      "Reuse cover for contracted curves; repair the stronger selection meeting but not contained in support."
    ],
    [
      [
        "Recover the structure sheaf",
        "Proper direct-image finiteness and normality recover the base ring; normalfinite verifies the algebraic core."
      ],
      [
        "Formal functions: open geometry",
        "Disconnected fibers produce compatible idempotents on infinitesimal neighborhoods; formal functions identifies their limit with the completed local ring."
      ],
      [
        "Local-ring contradiction: verified",
        "A local ring has only idempotents 0 and 1."
      ],
      [
        "Higher-dimensional crossing curve: needs repair",
        "Reuse curve coverage, then establish the crossing condition. This belongs only to part (2)."
      ]
    ]
  ]
});
entries.projection[4][1]=['Tensor counting of point divisors: verified','The finite local length of S_q⊗_R(R/𝔪_p) gives actual multiplicity; residue-degree-weighted counting multiplies by the function-field degree.'];
Object.assign(entries,{
  "strict": [
    "Strict transforms and prime-divisor coefficients",
    "D=Σa_P[P] is a finite formal sum of prime divisors. The unique strict transform Q̃ pushes to Q; exceptional prime divisors push to zero, so coeff_Q(f_*D)=coeff_Q̃(D).",
    "Here a cycle is simply the formal sum underlying the divisor. Construct actual strict transforms and the codimension-one isomorphism, and select geometric dimension weights. Actual cycle-pushforward formulas and residue degree one under a stalk isomorphism are already verified.",
    [
      "Exact fact: for proper birational f:X→Y with Y normal, every prime-divisor generic point η_Q has an open neighborhood U over which f is an isomorphism.",
      "The unique strict transform Q̃ has function field k(Q), hence f_*[Q̃]=[Q].",
      "If codim_Y f(P)≥2, the prime divisor P contributes zero to divisor pushforward.",
      "Additivity of D=Σa_P[P] gives coeff_Q(f_*D)=coeff_Q̃(D)."
    ],
    [
      [
        "Specify the object",
        "D is a finite real-coefficient formal sum of actual prime divisors."
      ],
      [
        "Construct the strict transform",
        "Take the corresponding point over η_Q in the isomorphism neighborhood and then its closure. This geometric neighborhood remains open."
      ],
      [
        "Compute pushforward",
        "The isomorphism gives degree one; contracted divisors drop dimension and contribute zero. Actual AlgebraicCycle.map formulas are verified."
      ],
      [
        "Conclude for negative components",
        "Effective f_*D forces all nonexceptional coefficients nonnegative, so negative components must be exceptional."
      ]
    ]
  ]
});

Object.assign(entries,{
  "codimone": [
    "Codimension-one isomorphism over a normal base",
    "A proper birational f:X→Y is an isomorphism over one open containing every codimension-one point of Y. The corresponding point is unique, its stalk map is an isomorphism, and codimension one is preserved.",
    "The complete geometric existence proof is verified on actual integral Schemes, coheight and stalks. It constructs the generic valuative square and spreads its lift to a section; neither the neighborhood nor stalk isomorphism is assumed.",
    [
      "X,Y integral; Y locally Noetherian; f proper.",
      "The given morphism is an isomorphism over some nonempty open: the definition of BirationalMorphism used here.",
      "Actual stalks of Y are integrally closed, expressing normality. The conclusion open is not an input."
    ],
    [
      [
        "Codimension one gives a DVR",
        "Use the actual coheight/stalk-dimension identity and normality."
      ],
      [
        "Construct and lift the generic square",
        "Use the inverse on the birational open, then properness for the actual DVR square."
      ],
      [
        "Spread the section and prove it is inverse",
        "Separatedness gives a closed section; its generic image is dense, and the source is reduced."
      ],
      [
        "Union of neighborhoods",
        "Glue the isomorphisms by Zariski locality over the union of all codimension-one neighborhoods."
      ],
      [
        "Corresponding prime point and local ring",
        "Prove the actual stalk map is an isomorphism, preserve coheight one and prove uniqueness of the preimage."
      ]
    ]
  ],
  "cover": [
    "Contracted curves through exceptional closed points",
    "For a projective birational map to a normal base, every exceptional closed point lies on a complete contracted curve.",
    "Follow Zariski main: the center is the complement of the maximal isomorphism open. Every point over the center is non-quasi-finite. Obtain a positive-dimensional fiber component through the specified point, then cut a curve. A positive-dimensional component somewhere in the fiber is insufficient. The general center-point criterion and curve construction remain open.",
    [
      "f projective birational, target normal; x an exceptional closed point and y=f(x).",
      "Exact Zariski main consequence: quasi-finiteness at any preimage of y gives an isomorphism neighborhood of y, using normality and properness.",
      "Use positive local fiber dimension at x, then hyperplanes through x in that projective component."
    ],
    [
      [
        "Specify the center",
        "Center=Y minus the maximal isomorphism open. The undefined rational inverse is distinct from the actual fiber f⁻¹(y)."
      ],
      [
        "Zariski main: geometric bridge",
        "A quasi-finite local map comes from a finite algebra; birationality embeds it in the fraction field and normality identifies it with the base. Spread the section and use proper/separated."
      ],
      [
        "Local positive dimension: geometric bridge",
        "Local fiber dimension zero implies quasi-finiteness at x, contradicting y being in the center."
      ],
      [
        "Curve through the closed point: open construction",
        "Cut the positive-dimensional projective component by hyperplanes through x to obtain a complete contracted curve."
      ]
    ]
  ],
  "intersection": [
    "Actual intersection and positivity",
    "For a complete curve C contracted by f: −D being f-nef gives D·C≤0; −E being f-ample gives E·C<0. Actual effective-divisor degree must still provide the support signs.",
    "The relative nef sign is its definition; the linear negation is verified separately. Relative ampleness restricts to an ample line bundle on a complete fiber curve, giving positive degree. Strict curve positivity is not claimed equivalent to geometric ampleness. Actual intersection and effective-divisor positivity remain open.",
    [
      "C must be a complete contracted curve; −D f-nef and −E f-ample.",
      "Construct intersection from the actual degree of 𝒪(D)|C and connect ample restrictions.",
      "Effective B and C not contained in its support imply B·C≥0; also meeting the support gives B·C>0."
    ],
    [
      [
        "Relative test curves",
        "Only contracted curves occur in the nef definition; the negative-sign equivalence is verified."
      ],
      [
        "Restriction of relative ampleness",
        "The ample restriction has positive degree; its numerical negative-sign consequence is verified."
      ],
      [
        "Effective-divisor positivity: open geometry",
        "Actual multiplicities are nonnegative; meeting the support supplies a positive one."
      ]
    ]
  ],
  "chow": [
    "Chow modification and geometric identities",
    "Follow Hartshorne: construct a projective modification, then normalize. The graph-closure properness, birationality and surjectivity are verified; projectivity and complete geometric identities remain open.",
    "The actual graph image and projections are constructed. Remaining tasks are the finite affine-cover projective construction, its projectivity, finite normalization, global intersection and Cartier push-pull. The modification existence is not assumed and then labeled complete.",
    [
      "Verified: graph closure from a nonempty open into a proper auxiliary space, with proper birational surjective modification.",
      "Open: Hartshorne’s finite affine cover and projective embeddings, proof of projectivity, then normalization.",
      "Open: actual Cartier projection, push-pull, effectivity and support pullback."
    ],
    [
      [
        "Graph closure: verified",
        "Use the actual scheme-theoretic image in X×_S P and its projections."
      ],
      [
        "Finite cover and projectivity: open",
        "Combine Hartshorne’s affine-cover projective embeddings; a proper projection alone does not prove this step."
      ],
      [
        "Normalization and geometric identities: open",
        "Connect finite normalization and actual Cartier degree/support to the verified descent logic."
      ]
    ]
  ],
  "modsurj": [
    "Surjectivity of proper birational morphisms",
    "A proper birational morphism to an integral scheme is surjective.",
    "Actual Scheme maps: the nonempty isomorphism open is dense, and properness makes the image closed. Surjectivity is proved, not assumed.",
    [
      "Y integral, f proper and an isomorphism over a nonempty open."
    ],
    [
      [
        "Dense image",
        "The image contains the dense isomorphism open."
      ],
      [
        "Closed image",
        "A proper map is closed, so its dense image is the whole target."
      ]
    ]
  ],
  "hartshornegraph": [
    "Hartshorne: actual graph closure",
    "The graph closure of U→P in X×_S P gives proper birational surjective Z→X and proper Z→P.",
    "The actual scheme-theoretic image is verified. The proper auxiliary P and map on U are inputs to this construction; building the finite family and proving projectivity remain part of the full Chow lemma.",
    [
      "X integral with Noetherian topology; X→S and P→S proper.",
      "A nonempty open U and actual map g:U→P commuting over S."
    ],
    [
      [
        "Actual image",
        "Construct the graph morphism and its scheme-theoretic image."
      ],
      [
        "Birationality",
        "The image map is a dense open immersion; its open section gives an isomorphism over U."
      ],
      [
        "Properness and surjectivity",
        "Compose the closed immersion with proper projections; the closed dense image covers X."
      ]
    ]
  ],
  "relativesigns": [
    "Relative nef and curve-positive negation signs",
    "On contracted curves, nef(−D) iff D·C≤0; curvePositive(−E) iff E·C<0.",
    "Verified relative numerical definitions and linear negation. CurvePositive means strictly positive degrees on contracted curves, and is not claimed equivalent to geometric f-ampleness.",
    [
      "A predicate for contracted curves and linear intersection maps.",
      "Applying this to f-ample requires its positive-degree restriction to complete fiber curves."
    ],
    [
      [
        "Restrict the test curves",
        "Quantify only over contracted curves."
      ],
      [
        "Linear negation",
        "Rewrite degree(−D)=−degree(D) to obtain the nonpositive/strictly negative signs."
      ]
    ]
  ],
  "ratproduct": [
    "Principal degree zero over k(t)",
    "Count irreducible factors with multiplicity and polynomial-degree weights. Finite zero/pole contributions plus the order at infinity sum to zero.",
    "Uses actual RatFunc, normalizedFactors and inftyValuation. This is the base k(t) calculation for the norm route. General-curve norm transport, place identification and line-bundle degree remain open.",
    [
      "k any field and a∈k(t) nonzero.",
      "Finite contributions are the degree sums of actual numerator and denominator factors, with multiplicities."
    ],
    [
      [
        "Finite places",
        "The degrees of actual irreducible factors sum to the polynomial degree."
      ],
      [
        "Infinity",
        "The actual infinity valuation gives ord∞(a)=−intDegree(a)."
      ],
      [
        "Sum to zero",
        "Finite contributions cancel the infinity order."
      ]
    ]
  ],
  "normalsections": [
    "Normal stalks imply normal affine coordinate rings",
    "If the actual stalks of an integral scheme are integrally closed, every nonempty affine-open coordinate ring is integrally closed.",
    "Identify actual affine Scheme stalks with prime localizations of the coordinate ring, then apply the local criterion for integral closure. Normal coordinate rings are not assumed.",
    [
      "Y integral with all actual stalks integrally closed.",
      "A nonempty affine open U."
    ],
    [
      [
        "Actual localizations",
        "For each maximal ideal, use hU.fromSpec and its actual stalk."
      ],
      [
        "Local normality criterion",
        "All maximal localizations are integrally closed, so Γ(Y,U) is integrally closed."
      ]
    ]
  ]
});
entries.dvrfoundation[2]='The actual stalk DVR theorem is integrated. codimone now derives the DVR hypothesis directly from geometric coheight one and the stalk-dimension identity.';
entries.valuative[2]='Actual proper/separated valuative criteria are verified. codimone now constructs the birational generic square, spreads the lift and proves the neighborhood isomorphism.';
entries.localorder[2]='DVR orders and residue degrees are verified. codimone now supplies actual codimension-one stalk isomorphisms from proper birational geometry; identifying actual Cartier coefficients remains open.';
entries.strict[2]='The actual codimension-one isomorphism open, unique corresponding prime point and stalk isomorphism are verified. Remaining tasks are its closure as the geometric strict transform, dimension weights and Cartier coefficients. Actual Scheme-cycle pushforward formulas can be reused.';
entries.strict[4][1][1]='The actual isomorphism open, unique codimension-one preimage and stalk isomorphism are constructed. Connect the closure of that point to the geometric prime divisor.';
entries.projection[4][2][1]='Follow norms and valuations: use the verified k(t) principal degree zero, prove ord_p(Na)=Σ_q f_q ord_q(a), identify all closed points of the complete curve, and define line-bundle degree independently of the rational section.';

entries.pushpull[2]='Actual cycle coefficient push-pull is verified, and the codimension-one isomorphism open and stalks are now proved from normal proper birational geometry. Actual Cartier local equations and pullback Weil cycles, prime-point closures and dimension weights still need to instantiate the identity.';

Object.assign(entries,{
  "localcartier": [
    "Cartier equations and actual Weil divisors",
    "Construct a mathlib Weil divisor from Cartier equations on an actual integral normal locally Noetherian Scheme. Unit transitions glue the orders; support is locally finite and the result is independent of equivalent presentations.",
    "Actual geometric construction is verified. The input atlas is Cartier local-equation data: nonzero rational equations and units in actual stalks. Coefficient equality, finite support and an existing Weil cycle are not assumed. Support is globally finite on a quasi-compact scheme.",
    [
      "X integral and locally Noetherian, with actual integrally closed stalks.",
      "Cartier data: affine cover, nonzero rational equations, and actual local unit transitions."
    ],
    [
      [
        "Glue by units",
        "Actual regular units have order zero, so chart coefficients agree."
      ],
      [
        "Prove local finiteness",
        "In any dimension, support lies in finitely many height-one primes containing the numerator or denominator."
      ],
      [
        "Construct the Weil divisor",
        "Glue actual orders into AlgebraicCycle and prove codimension-one support."
      ],
      [
        "Presentation independence",
        "Equivalent unit equations on different covers yield the same actual Weil divisor."
      ]
    ]
  ],
  "strict": [
    "Actual strict transforms and pushforward coefficients",
    "Construct the strict-transform injection on actual codimension-one generic points. Actual cycle pushforward reads its coefficient; ExceptionalIndex means the image is not codimension one.",
    "The original finite-support model is instantiated: weilCycleCoefficients_pushforward identifies birationalPush with actual AlgebraicCycle.map. Prime divisors are represented by generic points, as in mathlib cycles. Neither the strict injection nor multiplicity one is assumed.",
    [
      "X and Y integral; Y locally Noetherian with integrally closed actual stalks.",
      "A proper birational morphism. Quasi-compact X and Y are used for finite coefficient vectors."
    ],
    [
      [
        "Construct strict transforms",
        "Choose the unique actual prime point from the codimension-one isomorphism theorem."
      ],
      [
        "Identify exceptional primes",
        "The strict-transform image is exactly source primes mapping to codimension one."
      ],
      [
        "Compute actual coefficients",
        "Unique preimages and residue degree one give coeff_Q(f_*D)=coeff_Q̃(D)."
      ],
      [
        "Instantiate the original model",
        "Use actual finite cycle support to construct Finsupp and identify birationalPush."
      ]
    ]
  ],
  "pushpull": [
    "Actual real Cartier push-pull identity",
    "Actual Cartier pullback along a proper birational morphism of integral normal schemes satisfies f_*(f*D)=D, including finite real combinations.",
    "Actual pullback atlases and Weil cycles are constructed. Coefficient equality and multiplicity one follow from actual codimension-one stalk isomorphisms. Uses actual coheight weights and AlgebraicCycle.map; no hleft, hcoeff, arbitrary lifted cycle or exceptional-weight assumption.",
    [
      "X and Y integral, normal and locally Noetherian; f proper birational.",
      "D is a finite real combination of actual Cartier atlases. Pullback atlases are constructed in the proof."
    ],
    [
      [
        "Construct actual pullback",
        "Choose affine neighborhoods inside inverse-image charts and prove local unit compatibility."
      ],
      [
        "Compare codimension-one orders",
        "Actual isomorphic stalks preserve the DVR order of pulled-back equations."
      ],
      [
        "Actual cycle push-pull",
        "Unique codimension-one preimages have residue degree one; other weights contribute zero."
      ],
      [
        "Real coefficients",
        "Prove the identity directly for finite real combinations of actual Cartier cycles."
      ]
    ]
  ],
  "effdown": [
    "Actual real Cartier effectivity descent",
    "Construct actual pullback: effectivity of its Weil cycle implies effectivity of the original real Cartier Weil cycle.",
    "Push-pull is established inside the proof; hleft is no longer required. Effective pullback is the mathematical condition when applying descent, not an open bridge. The projective negativity theorem producing that condition remains open.",
    [
      "A proper birational map of integral normal locally Noetherian schemes.",
      "D is a finite real combination of actual Cartier atlases.",
      "When applying descent, the constructed pullback is effective."
    ],
    [
      [
        "Construct and prove push-pull",
        "Internally prove f_*(f*D)=D for the constructed real Cartier pullback."
      ],
      [
        "Push forward effective cycles",
        "Actual cycle pushforward preserves nonnegative coefficients; use the proved identity."
      ]
    ]
  ],
  "rationalorder": [
    "DVR order of actual rational equations",
    "The order of a nonzero fraction-field element is representation-independent, additive under multiplication and unchanged by actual local unit transitions.",
    "Uses actual IsFractionRing numerators and denominators and DVR addVal, rather than an arbitrary pairing.",
    [
      "An actual DVR R with fraction field K; a nonzero rational equation in K."
    ],
    [
      [
        "Representation independence",
        "Every nonzero numerator/denominator representation gives the same order."
      ],
      [
        "Unit transitions",
        "Actual local units have zero order; multiplicativity gives transition invariance."
      ]
    ]
  ],
  "divisorsupport": [
    "Cartier support finiteness in every dimension",
    "A nonzero Noetherian-domain element belongs to finitely many height-one primes. Actual affine Scheme codimension-one nonunit-germ points are finite.",
    "Proved using finitely many minimal primes over a principal ideal. No Dedekind-ring restriction or finite-support input.",
    [
      "A nonzero section on a nonempty affine open of an integral locally Noetherian scheme."
    ],
    [
      [
        "Minimal primes",
        "Height-one primes containing r are minimal over (r)."
      ],
      [
        "Actual affine points",
        "Identify ideal height and nonunit germs with geometric coheight and prime membership."
      ]
    ]
  ],
  "cartierpullback": [
    "Actual Cartier equation pullback",
    "Construct function-field pullback and Cartier pullback atlases from a dominant Scheme morphism; prove the generic/local-ring square, unit transitions and order invariance at isomorphic stalks.",
    "The affine cover and rational equations are constructed. Compatibility follows from actual stalkSpecializes_stalkMap, rather than a supplied pullback cycle or compatibility equality.",
    [
      "An actual dominant morphism between integral schemes and a Cartier equation atlas.",
      "Normal locally Noetherian schemes and an actual stalk isomorphism for order comparison."
    ],
    [
      [
        "Function-field pullback",
        "Dominant morphisms map actual generic points to generic points."
      ],
      [
        "Actual commuting square",
        "Generic pullback commutes with actual local-ring maps."
      ],
      [
        "Pullback atlas",
        "Choose affine inverse-image neighborhoods and prove unit transitions for pulled-back equations."
      ],
      [
        "Order comparison",
        "Pulled-back fractions and actual stalk isomorphisms preserve DVR order."
      ]
    ]
  ]
});
entries.negative[2]='The coefficient implication is verified. strict now constructs actual strict transforms and identifies ExceptionalIndex with source primes whose image is not codimension one.';
entries.chow[2]='Actual Cartier pullback, Weil cycles, real-coefficient push-pull and effectivity descent are verified. The Hartshorne finite-affine-cover projectivity construction, finite normalization and curve-intersection/support properties remain open.';
entries.chow[3][2]='Actual real Cartier push-pull and effectivity descent are verified. Curve projection, support preimages and finite normalization remain open.';
entries.localorder[2]='DVR orders and residue degrees are verified. Actual Cartier atlases, function-field pullback and strict transforms now identify geometric coefficients and prove push-pull.';
entries.projection[2]+=' Actual Cartier equation pullback and underlying Weil cycles are now verified; complete-curve line-bundle degree and intersection compatibility remain open.';
entries.chow[4][2][1]='Finite normalization, curve projection and support preimages remain open. Actual real Cartier pullback, push-pull and effectivity descent are verified.';
export function translateNodes(nodes){return nodes.map(n=>{if(!english)return n;const [title,statement,scope,inputs,steps]=entries[n.id];return {...n,title,statement,scope,inputs,steps:steps.map((s,i)=>[...s,n.steps[i]?.[2]])};});}
const pairs=[['展开纸牌','Spread cards'],['折叠纸牌','Stack cards'],['展开输入','Expand inputs'],['收起输入','Collapse inputs'],['所选及直接前提','Selected + direct premises'],['设置','Settings'],['阅读设置','Reading settings'],['字号独立于图谱缩放，设置自动保存在本机。','Font size is independent of graph zoom. Settings are saved locally.'],['节点字号','Node font size'],['证明详情字号','Proof detail font size'],['工具栏字号','Toolbar font size'],['详情面板宽度','Detail panel width'],['数学证明的阅读预览','Mathematical proof reading preview'],['恢复默认','Reset defaults'],['中文 / EN','ZH / EN'],['基础输入','Base inputs'],['结论','Result'],['显示全部 · Home','Frame all · Home'],['显示全部','Frame all'],['聚焦所选 · 小数点键','Frame selected · decimal key'],['聚焦所选','Frame selected'],['放大','Zoom in'],['缩小','Zoom out'],['缩放比例','Zoom level'],['节点编辑区：拖动空白平移，滚轮缩放，Home 显示全部，小数点键聚焦。','Node editor: drag the background to pan, wheel to zoom, Home to frame all, decimal key to frame selected.'],['关闭','Close'],['详情','Details'],['节点工作区参考 ','The workspace follows '],[' 的接口连线与视图导航。形式化图谱参考 ',' sockets, links and view navigation. The proof atlas is inspired by '],['个已验证定理','verified theorems'],['证明步骤与依赖','Proof steps and dependencies'],['中英文阅读','Bilingual reading'],['首个形式化项目','FIRST FORMALIZATION PROJECT'],['从数学证明到 Lean','From mathematics to Lean'],['打开工作区 ↗','Open workspace ↗'],['只看直接前提','Direct premises only'],['切换中英文','Switch language'],['全屏显示','Fullscreen'],['放大三维图','Zoom in'],['缩小三维图','Zoom out'],['可点击的证明依赖图','Interactive proof dependency graph'],['图谱视角','Graph view'],['所选证明步骤','Selected proof step'],['节点详情','Node details'],['Negativity lemma 原始证明 PDF','Negativity lemma original proof PDF'],['三维证明依赖图。拖动旋转，滚轮缩放；键盘方向键旋转，加减键缩放。','3D proof dependency graph. Drag to orbit, wheel to zoom. Arrow keys rotate; plus/minus zoom.'],['返回主页 ↗','Homepage ↗'],['数学 · 证明 · 可追溯的验证','MATHEMATICS · PROOFS · TRACEABLE VERIFICATION'],['看见证明的每一层。','See every layer of a proof.'],['从一条定理出发，沿着依赖追问：它用了什么？哪些推导已经通过 Lean，哪些几何结论仍作为假设？','Start with a theorem and follow its premises: which steps are verified in Lean, and which geometric results remain assumptions?'],['负性引理 · 从有限系数到双有理几何','Negativity · from finite coefficients to birational geometry'],['数值与系数核心已验证；几何接口仍待接入。点击节点，深入证明依赖、原始论证和 Lean 源码。','Numerical, coefficient and descent arguments are verified. Geometric interfaces remain open. Explore dependencies, original arguments and Lean source.'],['◐ 部分完成 · 条件式定理已验证','◐ In progress · conditional theorems verified'],['有限系数','Finite coefficients'],['几何假设','Geometric inputs'],['条件式 negativity','Conditional negativity'],['完整几何定理','Full geometric theorem'],['探索证明图谱 ↗','Explore the proof atlas ↗'],['如何读这张证明地图','Reading the proof atlas'],['“暂作假设”表示一个尚未从几何定义证明的输入，不表示代码中新增了 axiom。每个已验证节点都附有对应源码与验证记录。','An assumed input has not yet been proved from geometric definitions; it is not a new Lean axiom. Each verified node links to source and evidence.'],['查看验证依据 →','Verification evidence →'],
['形式化验证','Formalization'],['证明图谱','Proof atlas'],['原始证明','Original proof'],['验证记录','Verification evidence'],['一条证明，沿依赖逐层展开。','Explore a proof through its dependencies.'],['数值核心已通过 Lean。完整的几何定理仍在建设中。','The numerical core is verified in Lean. The full geometric theorem is under construction.'],['下载 Lean 工程 ↓','Download Lean project ↓'],['原始证明 PDF ↗','Original proof PDF ↗'],['证明依赖地图','Proof dependency atlas'],['点击结论查看它依赖的步骤，再点击依赖继续深入。箭头从前提指向结论。','Select a result to explore its premises. Arrows run from premises to conclusions.'],['展开图谱','Expand atlas'],['恢复分栏','Restore panels'],['✓ Lean 已验证',englishStatuses.done],['◐ 条件式证明 · 输入未齐',englishStatuses.conditional],['? 暂作假设',englishStatuses.assumption],['○ 待完成目标',englishStatuses.pending],['2D 平面','2D map'],['3D 空间','3D space'],['显示范围','Show'],['全图（弱化无关）','Full graph · dim unrelated'],['所选结论及其前提','Selected result and premises'],['仅看未完成几何输入','Open geometric inputs'],['← 返回上一节点','← Previous node'],['选中关系','Selection'],['◎ 当前结论','◎ Selected result'],['实线边框：直接前提','Solid border: direct premise'],['虚线边框：间接前提','Dashed border: indirect premise'],['淡化：非当前依赖','Dimmed: unrelated'],['当前结论','Selected result'],['直接前提','Direct premise'],['间接前提','Indirect premise'],['非当前依赖','Unrelated'],['01 · 数值与输入','01 · Coefficients and inputs'],['02 · 已验证的推导','02 · Verified deductions'],['03 · 几何目标','03 · Geometric goals'],['图谱为人工整理的数学依赖蓝图，不是 Lean 内核自动导出的全部常量依赖。','This is a curated mathematical blueprint, not a kernel-extracted constant dependency graph.'],['依赖与假设','Premises & assumptions'],['证明步骤','Proof steps'],['Lean 源码','Lean source'],['为了得到这个结论，先需要','Direct premises'],['尚需建立的几何内容','Remaining geometric inputs'],['当前输入 / 假设','Current inputs / hypotheses'],['沿这条路径，仍需承认的几何输入','Assumed geometric inputs on this path'],['琥珀色表示显式假设或待补的几何桥接，不是代码中的新增 axiom。','Amber marks explicit hypotheses or open geometric bridges, not new Lean axioms.'],['接下来哪些结论使用它','Results using this node'],['这是当前图谱的最终目标。','This is a final goal in the current atlas.'],['没有其他项目节点；使用 mathlib 基础与下列明确输入。','No other project nodes; uses mathlib foundations and the explicit inputs below.'],['此依赖链没有未证明的几何输入；定理的定义条件仍须满足。','This path has no unproved geometric inputs; the theorem’s defining conditions still apply.'],['已验证源码的阅读导览','Guide to verified source'],['原始数学证明 / 待完成计划','Mathematical proof / open plan'],['非实时 Lean 执行','Not a live Lean session'],['← 上一步','← Previous'],['下一步 →','Next →'],['对应原始证明 ↘','Corresponding original proof ↘'],['对应形式化节点 →','Related formalization node →'],['此节点尚无完成的 Lean 几何证明。图中的中文论证不能替代形式化验证。','This node has no completed geometric Lean proof. The explanatory argument is not a formal verification.'],['阅读原始证明 →','Read original proof →'],['正在读取源码快照…','Loading source snapshot…'],['缺少对应源码，不能展示验证标记。','Source is missing; verification cannot be displayed.'],['下载源码','Download source'],['GitHub 定位 ↗','View on GitHub ↗'],['第 ','line '],[' 行',''],['参数假设请看定理完整类型。依赖仅含 Lean 常用基础公理，不意味着这些参数假设已从几何得到证明。','Read the complete theorem type for parameter hypotheses. Foundational axiom checks do not prove those hypotheses from geometry.'],['重置视角','Reset view'],['聚焦依赖链','Focus premises'],['定位节点','Locate node'],['横向：证明类别 · 纵向：步骤位置','Horizontal: proof category · Vertical: step position'],['纵深：依赖推导层级','Depth: deduction level'],['拖动旋转 · 滚轮或 ＋／− 缩放 · 点击节点查看证明。3D 层次仅表示推导深度，验证状态仍由颜色表示。','Drag to rotate · Wheel or ＋／− to zoom · Select a node to read the proof. Depth indicates deduction level; colors indicate verification status.'],['每一个“已验证”，都有明确范围。','Every verification claim has a precise scope.'],['正在读取验证记录…','Loading verification evidence…'],['个已验证定理','verified theorems'],['公理检查无 sorryAx','Axiom audit: no sorryAx'],['当前源码快照 · 本地验证','Current source snapshot · verified locally'],['验证日期 · 中国标准时间','Checked at · China Standard Time'],['公理依赖：','Axiom dependencies: '],['。没有新增几何公理；未完成内容仍是显式参数或规划节点。','. No new geometric axioms; open geometry remains in explicit parameters or planning nodes.'],['完整验证日志 ↗','Verification log ↗'],['源码 SHA-256 清单 ↗','Source SHA-256 manifest ↗'],['公理检查脚本 ↗','Axiom audit script ↗'],['公开源码的指纹','Public source fingerprints'],['验证记录加载失败，请刷新或下载工程核查。','Evidence failed to load. Refresh or download the project.'],['源码快照加载失败。','Source snapshot failed to load.'],['复现编译与公理检查','Reproduce the build and axiom audit'],['设计参考与图谱语义','Design references and graph semantics'],['在此页展开原始 PDF','Open original PDF on this page'],['阅读原版 PDF ↗','Read original PDF ↗'],['下载原始 LaTeX ↓','Download original LaTeX ↓'],['GitHub 源码 ↗','GitHub source ↗'],['← 形式化验证','← Formalization'],['构造有效的相对反 ample 除子','Construct an effective relatively anti-ample divisor'],['exceptional locus 被支撑包含','Support contains the exceptional locus'],['取最大比值，得到矛盾','Maximum ratio and contradiction'],['每个纤维全在支撑内，或完全不相交','Each fiber is contained in the support or disjoint from it'],['从 projective 推广到 proper','From projective to proper'],['以下是原稿的阅读导览。完整表述、符号与证明以随附的 PDF / LaTeX 原稿为准；下方不是新增的 Lean 验证结果。','This is a reading guide to the original note. Consult the attached PDF / LaTeX for full statements and proofs; this guide is not additional Lean verification.'],['在仿射底 Y 上，取 f-ample Cartier 除子 A。双有理性使 f∗O(−A) 泛秩为一，故存在非零全局截面 s。令 E = −A + div(s)，则 E 有效且 −E 相对 ample。','Over an affine base Y, choose an f-ample Cartier divisor A. Birationality makes f∗O(−A) generically rank one, so it has a nonzero global section s. Set E=−A+div(s); E is effective and −E relatively ample.'],['正规底上的 exceptional locus 被压缩曲线覆盖。对每条这样的曲线 C，E·C < 0；E 的有效性迫使 C 包含在 Supp E 中。','Over a normal base, contracted curves cover the exceptional locus. Each such curve has E·C < 0, so effectivity forces it into Supp E.'],['假设 f∗D 有效而 D 不有效。负系数分量是 exceptional，且 E 在其上系数为正。取 e = max(−coeffᵢ(D)/coeffᵢ(E))。则 D+eE 有效，并在某个负分量 F 上系数为零。','Assume f∗D is effective and D is not. Negative components are exceptional, with positive E-coefficients. Set e=max(−coeffᵢ(D)/coeffᵢ(E)); D+eE is effective and vanishes at a negative component F.'],['取 F 中不被其支撑包含的压缩曲线 C，于是 0 ≤ (D+eE)·C = D·C + e(E·C) < 0，矛盾。','Choose a contracted curve C in F outside the shifted support. Then 0 ≤ (D+eE)·C=D·C+e(E·C)<0, a contradiction.'],['由连通纤维性质，若纤维遇到 Supp D 却不包含于其中，可找到纤维内与支撑相交但不被其包含的曲线 C。此时 D·C > 0，与 −D 相对 nef 矛盾。','Connected projective fibers supply a curve C meeting but not contained in Supp D whenever a fiber partly meets it. Then D·C>0, contradicting relative nefness of −D.'],['用 Chow 引理与正规化取 π : X′ → X，使复合态射 projective。对 D′ = π∗D 应用射影版本，再用投影公式、π∗D′ = D 和支撑的拉回及纤维满射下降结论。','Apply Chow’s lemma and normalization to obtain π:X′→X with projective composite. Apply the projective theorem to D′=π∗D, then descend using projection, push-pull, support preimages and surjectivity.'],['工程固定 Lean 和 mathlib 版本。网页不执行 Lean；此处展示的是已完成的本地编译记录和精确源码快照。条件式定理的参数假设不会出现在 #print axioms 中，必须同时阅读其完整类型。','The project pins Lean and mathlib versions. This page displays local build evidence and exact source snapshots. Conditional theorem parameters do not appear in #print axioms; read their full types as well.'],['参考 ','Inspired by '],[' 的依赖导航、',' dependency navigation, '],[' 的逐步证明阅读，以及实验性 ',' stepwise proof reading, and experimental '],[' 对验证证据、假设和未完成工作的区分。本页为独立实现，没有集成这些工具的验证后端。',' distinctions between verification, hypotheses and open work. This independent page does not integrate their verification backends.'],['绿色：定理已通过 Lean，具体几何或模型范围见节点；蓝绿色：带显式几何接口假设的定理已编译；琥珀色：尚未证明的输入；灰色：完整目标未完成。连线表示阅读与形式化规划中的前提关系，几何假设节点的边不是内核公理依赖。','Green: Lean-verified theorem; read each node for its geometric or model scope. Cyan: verified theorem with explicit interface hypotheses. Amber: unproved input. Gray: open geometric goal. Edges show curated proof premises, not kernel axiom dependencies.']
];
const sorted=pairs.sort((a,b)=>b[0].length-a[0].length);
export function t(text){if(!english)return text;for(const [zh,en] of sorted)text=text.split(zh).join(en);return text;}
export function installLanguage(){document.documentElement.lang=english?'en':'zh-CN';document.title=document.querySelector('#graph')?(english?'Negativity · Interactive proof atlas':'Negativity · 交互式证明图谱'):(english?'Formalization · Sheng Meng':'形式化验证 · Sheng Meng');const button=document.querySelector('#languageToggle');button.textContent=english?'中文':'EN';button.onclick=()=>{localStorage.setItem('formalization-language',english?'zh':'en');const u=new URL(location);u.searchParams.set('lang',english?'zh':'en');location.href=u;};if(!english)return;
function translate(root){if(root.nodeType===3){if(root.parentElement?.closest('script,style,pre,code'))return;const value=t(root.nodeValue);if(value!==root.nodeValue)root.nodeValue=value;return;}if(root.nodeType!==1)return;for(const el of [root,...root.querySelectorAll('*')])for(const attr of ['aria-label','title','data-tip','alt'])if(el.hasAttribute(attr))el.setAttribute(attr,t(el.getAttribute(attr)));const walker=document.createTreeWalker(root,NodeFilter.SHOW_TEXT);let n;while(n=walker.nextNode())translate(n);}
translate(document.body);new MutationObserver(records=>{for(const r of records){if(r.type==='characterData')translate(r.target);else r.addedNodes.forEach(translate);}}).observe(document.body,{subtree:true,childList:true,characterData:true});}

entries.fiberdown[2]='Only set-theoretic descent is proved: surjectivity, support preimages and the upper fiber dichotomy are hypotheses. The upper geometric dichotomy and the higher-dimensional curve step remain open. This is not a complete proof of Theorem 1.4(2).';
pairs.push(['完整 negativity lemma 尚未形式化完成','The complete negativity lemma is not yet formalized'],['代码编译通过 ✓','Code compiled successfully ✓'],['个已编译定理声明（含条件式）','compiled theorem declarations (including conditional proofs)'],['设定：任意特征的代数闭域 k；variety 为整的、分离的有限型 k-scheme。D 为 ℝ-Cartier 除子；nef 和 ample 均相对于 f，交数在曲线正规化上取线丛次数。完整约定已补入 PDF 与 LaTeX 原稿。','Setting: an algebraically closed field k of arbitrary characteristic; varieties are integral separated finite-type k-schemes. D is R-Cartier; nefness and ampleness are relative to f. Intersections are degrees on normalized curves. Full conventions are included in the PDF and LaTeX note.']);

Object.assign(entries,{
  "affinedivisor": [
    "Pointwise pullback and degree of finite divisors",
    "For an actual finite map of affine normal curves, tensor-length point multiplicities extend to arbitrary finite signed divisors, and deg(h*D)=[L:K]deg(D) is proved.",
    "Here degree means the closed-point sum of a finite divisor, not yet the degree of an arbitrary line bundle on a complete curve. There is no separability or characteristic-zero restriction. Principal pullback, inverse-image support and effectivity descent are also proved.",
    [
      "An actual finite torsion-free extension R→S of Dedekind domains; flatness follows from torsion-freeness.",
      "Finite-type k-algebras R,S and their actual fraction fields K,L.",
      "Point multiplicities are actual tensor lengths; over an algebraically closed field all closed-point residue degrees are one."
    ],
    [
      [
        "Extend from points",
        "Extend genuine point pullbacks by additivity to arbitrary positive and negative integer coefficients."
      ],
      [
        "Check local equations",
        "From ord_q(h*a)=e_q ord_p(a), prove that principal-divisor pullback is the divisor of the pulled function."
      ],
      [
        "Count multiplicities over an algebraically closed field",
        "Zariski’s lemma gives residue degree one. The sum of tensor lengths equals [L:K], including inseparable degree."
      ],
      [
        "Support and positivity",
        "Pullback support is its inverse image. Effectivity is preserved and descends; a nonzero effective divisor has positive degree."
      ]
    ]
  ],
  "separablenorm": [
    "Prime ideal norms for separable extensions",
    "For a finite separable extension of Dedekind domains, N(P)=p^[k(P):k(p)]. The base fraction field need not be perfect.",
    "An auxiliary result for the norm route, requiring extension separability. Point-length counting does not use this requirement. This is not yet the product formula on a complete curve.",
    [
      "A finite torsion-free Dedekind extension.",
      "The fraction-field extension is separable; the actual maximal ideals P,p satisfy lying over."
    ],
    [
      [
        "Construct the normal closure",
        "Take the integral closure in an actual finite normal field extension."
      ],
      [
        "Compute in the Galois extension",
        "Apply the verified prime-ideal norm theorem."
      ],
      [
        "Descend through the tower",
        "Norm transitivity and residue-degree multiplicativity cancel the normal-closure power."
      ]
    ]
  ]
});
entries.projection[3]=['Verified: the pullback square, tensor lengths, finite-divisor degree pullback and principal-divisor compatibility.','Open: divisor representations of arbitrary complete-curve line bundles, representation-independent degree, normalization and the point-image case.','The main route is point-length counting, including inseparable maps; norms remain auxiliary.'];
entries.projection[4][1]=['Point counts and finite divisors: verified','Actual tensor lengths count multiplicities. Additivity extends the formula to finite signed divisors, and compatibility with principal divisors is proved.'];
entries.projection[4][2]=['Complete-curve line-bundle degree: open','Use affine neighborhoods locally, while keeping the global curves complete. Construct divisor representations and representation-independent degree, then connect normalization and the point-image case.'];

Object.assign(entries,{
  "normalfinite": [
    "Finite birational Scheme isomorphisms over a normal base",
    "A finite birational map of integral schemes to a normal target is an actual Scheme isomorphism. A finite fiber of a proper birational map also has an isomorphism neighborhood.",
    "The actual generic-stalk isomorphism constructs the function-field embedding. Normal affine rings give coordinate-map bijectivity, and affine inverses glue globally. The previous affine-reduction and gluing gap is closed.",
    [
      "Actual integral schemes X,Y and BirationalMorphism f.",
      "IsFinite f and integrally closed actual target stalks.",
      "The finite-fiber corollary requires properness and a finite point set of the fiber."
    ],
    [
      [
        "Construct the function-field embedding",
        "The birational isomorphism open gives an inverse generic-stalk map, embedding inverse-image sections into the actual target function field."
      ],
      [
        "Prove each affine map",
        "Finiteness gives integrality, normality gives surjectivity, and the function-field embedding gives injectivity."
      ],
      [
        "Glue globally",
        "Use the affine-open cover of Y and Zariski locality of Scheme isomorphisms."
      ],
      [
        "Finite-fiber neighborhood",
        "Apply the proper finite-fiber neighborhood theorem, restrict birationality and normality, and apply the global result."
      ]
    ]
  ],
  "zmtpoint": [
    "Zariski main: isomorphism near a quasi-finite point",
    "For a proper birational map to a normal target, one quasi-finite preimage point gives an isomorphism neighborhood of its image. Every exceptional fiber point is therefore nonisolated.",
    "The pointwise result is proved using actual relative normalization and mathlib’s Zariski main theorem. It is no longer a coverage input. A complete curve in the fiber is not constructed here.",
    [
      "Actual integral schemes X,Y and a proper birational map f.",
      "All actual target local rings are integrally closed.",
      "The neighborhood theorem takes f.QuasiFiniteAt x. The exceptional center is defined by the absence of a target isomorphism neighborhood."
    ],
    [
      [
        "Identify relative normalization",
        "On every affine open, birational embedding and normality identify the integral closure in inverse-image sections with the base ring. Glue globally."
      ],
      [
        "Apply pointwise Zariski main",
        "mathlib gives a toNormalization isomorphism near the specified point. Relative normalization is already Y, so transport the neighborhood to Y."
      ],
      [
        "Exclude quasi-finiteness pointwise",
        "An exceptional image belongs to no isomorphism open, so that preimage point cannot be quasi-finite."
      ],
      [
        "Actual fiber is nonisolated",
        "Quasi-finiteness is equivalent to its singleton being open in the actual fiber. Every exceptional singleton is not open."
      ]
    ]
  ],
  "cartiersupport": [
    "Effective Cartier support pullback and descent",
    "Actual effective Cartier pullback stays effective and Supp(p*D)=p⁻¹(Supp D). For proper birational modifications, the fiber-support alternatives upstairs and downstairs are equivalent.",
    "Effectivity and support use regular equations and units in actual local rings; chart independence is proved. This covers effective Cartier divisors. General effective R-Cartier support remains open, and the fiber alternative itself is not proved here.",
    [
      "A dominant map p of actual integral schemes and an effective CartierAtlas A.",
      "Effective means each rational local equation comes from a regular element of the actual local ring.",
      "Descent also requires p proper and birational; surjectivity and the support identity are proved from geometry."
    ],
    [
      [
        "Define actual support",
        "Nonunit local equations define support. Unit transitions prove independence from the chart."
      ],
      [
        "Local pullback reflects units",
        "The actual Scheme stalkMap is a local-ring map; a regular element pulls back to a unit exactly when it is a unit downstairs."
      ],
      [
        "Construct effective pullback",
        "Pull regular equations through actual stalk maps, outputting an effective CartierAtlas and the full inverse-image support identity."
      ],
      [
        "Connect actual fiber descent",
        "Proper birationality gives surjectivity. The proved support identity yields equivalence of disjointness or containment. The upstairs alternative still needs its own proof."
      ]
    ]
  ]
});
entries.cover[2]='Pointwise isomorphism and nonisolated exceptional fiber points are proved. Remaining: connect a nonisolated closed point to a positive-dimensional fiber component and construct a complete curve through that point.';
entries.cover[3]=['Verified: any quasi-finite preimage point gives a target isomorphism neighborhood for a proper birational map to a normal base; every exceptional fiber point is nonisolated.','Open: cut an actual complete curve through the specified closed point in a positive-dimensional projective fiber component.'];
entries.cover[4][1]=['Pointwise Zariski main: verified','Relative normalization is the normal base itself. mathlib’s pointwise neighborhood theorem therefore gives a target isomorphism open for the original map.'];
entries.cover[4][2]=['Each exceptional fiber point is nonisolated: verified','Quasi-finiteness is equivalent to an open singleton in the actual fiber. Exclude it at each point; positive-dimensional components and curves remain to be constructed.'];
entries.fiberdown[2]='Set-theoretic descent is proved. Surjectivity and inverse-image support are now proved for actual effective Cartier pullbacks. The upstairs fiber dichotomy and general effective R-Cartier support remain open; the full negativity lemma is not complete.';
entries.fiberdown[3]=['Verified: proper birational modifications are surjective.','Verified: actual effective Cartier support pullback and fiber descent. Open: general effective R-Cartier support.','Still open: the support alternative on every upstairs fiber. It is not assumed to be proved.'];
entries.fiberdown[4]=[['Actual Cartier support: verified','Construct effective pullback and its full inverse-image support identity; this identity is no longer a Cartier-case input.'],['Fiber equivalence: verified','Proper birational surjectivity gives equivalence of the support alternatives upstairs and downstairs.'],['Still to connect','Prove the upstairs fiber alternative and identify general effective R-Cartier support.']];
entries.chow[2]='Hartshorne graph closure, actual Cartier pullback, real-coefficient push-pull and effectivity descent are proved. Effective Cartier support pullback is now proved. Finite-cover projectivity, finite normalization, global curve intersections and general effective R-Cartier support remain open.';
entries.chow[3][2]='Verified: actual R-Cartier push-pull and effectivity descent, and effective Cartier inverse-image support. Open: global curve projection, general effective R-Cartier support and finite normalization.';
entries.chow[4][2][1]='Effective Cartier support pullback and actual R-Cartier push-pull are verified. Finite normalization, global curve intersections and general effective R-Cartier support remain open.';

Object.assign(entries,{
  "rcone": [
    "Effective real decomposition: rational cone and denominators",
    "For a rational coefficient matrix M, Mx≥0 gives x=Σwⱼzⱼ with nonnegative real wⱼ, integral zⱼ and Mzⱼ≥0. Every zero position of Mx stays zero in each Mzⱼ.",
    "The finite coefficient theorem proves exact decomposition, zero constraints and positive denominator clearing; none is an extra input. Nonnegative Weil coefficients have not yet been identified with regular Cartier local equations.",
    [
      "A finite rational family of generators and finitely many prime-coefficient positions.",
      "The original real combination has nonnegative coefficients. Its original real weights need not be nonnegative."
    ],
    [
      [
        "Preserve all zero coefficients",
        "A basis of the finite rational span of the real coordinates constructs a rational family satisfying every original zero-coefficient equation."
      ],
      [
        "Rational open cone",
        "Rational box vertices prove that every point of an open set lies in the convex hull of rational points inside that open set."
      ],
      [
        "Exact effective decomposition",
        "Impose positivity at the original positive positions while preserving equations at zero positions. This produces effective rational combinations."
      ],
      [
        "Positive denominator clearing",
        "Multiply by positive common denominators and adjust the real weights to obtain integral combinations."
      ]
    ]
  ],
  "rdecomp": [
    "Actual R-Cartier: nonnegative Weil decomposition",
    "An effective R-Cartier Weil cycle on a normal quasi-compact scheme is a nonnegative real sum of constructed Cartier presentations, each with nonnegative Weil coefficients and no new zero-position support.",
    "Integral combinations are constructed from actual local equations; actual Weil coefficients and the weighted cycle identity are proved. Nonnegative Weil coefficients must still imply regular local equations before full effective R-Cartier support pullback is obtained. The full negativity lemma remains open.",
    [
      "An actual integral locally Noetherian quasi-compact scheme whose actual stalks are integrally closed.",
      "Finitely many actual CartierAtlas presentations and arbitrary real weights.",
      "The original actual Weil cycle is effective. Individual input presentations or their original weights need not be effective."
    ],
    [
      [
        "Construct actual integral combinations",
        "Refine the finite family of chart opens to affine neighborhoods. Local equations and unit transitions are products of integral powers."
      ],
      [
        "Verify actual coefficients",
        "Actual DVR orders add on products and multiply on integral powers, proving the actual Weil-coefficient identity."
      ],
      [
        "Connect effective decomposition",
        "Finite Weil supports give the coefficient matrix. Apply rational-cone decomposition and construct the corresponding actual Cartier presentations."
      ],
      [
        "Remaining geometric bridge",
        "Nonnegative Weil coefficients must imply regular local equations via codimension-one extension on a normal Noetherian domain. Full support and pullback identification follows next."
      ]
    ]
  ]
});
entries.fiberdown[2]='Actual effective Cartier support pullback is proved. Rational-cone decomposition, actual integral combinations and nonnegative Weil decomposition for R-Cartier are now proved. Nonnegative Weil coefficients must still give regular local equations and full support; the upstairs fiber dichotomy also remains open. The complete theorem is not proved.';
entries.fiberdown[3][1]='Verified: effective Cartier support pullback and actual R-Cartier nonnegative Weil decomposition. Open: nonnegative Weil coefficients imply regular local equations and full support identification.';
entries.fiberdown[4][2]=['R-Cartier decomposition: verified','Actual Cartier presentations with nonnegative Weil coefficients are constructed, preserving every original zero coefficient.'];
entries.fiberdown[4].push(['Still to connect','Prove regular local equations and full support from nonnegative Weil coefficients, and complete the upstairs fiber dichotomy.']);
entries.chow[2]='Effective Cartier support pullback, actual R-Cartier push-pull and nonnegative Weil decomposition are proved. Finite-cover projectivity, finite normalization, global curve intersections, local extension from nonnegative Weil coefficients and general R-Cartier full support remain open.';

Object.assign(entries,{
  "normalext": [
    "Codimension-one extension on a normal domain",
    "In a normal Noetherian domain R, a fraction belongs to R exactly when it is regular at every height-one prime.",
    "The ring-theoretic extension theorem is proved. Height-one associated primes and actual local DVRs are outputs, not an assumed intersection identity. Arbitrary characteristic is allowed.",
    [
      "An actual normal Noetherian domain and its fraction field.",
      "The fraction is regular at all height-one localizations."
    ],
    [
      [
        "Determinant trick",
        "An annihilator witness in a principal quotient gives a principal maximal ideal using integral closedness."
      ],
      [
        "Associated primes",
        "Localize at an actual associated prime and prove the local ring is a DVR, hence its height is one."
      ],
      [
        "Detect divisibility",
        "A nonzero class in a principal quotient produces a height-one associated prime detecting failure of divisibility."
      ],
      [
        "Extend the fraction",
        "Choose actual numerator and denominator and apply the proved height-one divisibility criterion."
      ]
    ]
  ],
  "cartiereff": [
    "Actual Cartier effectivity: the Weil criterion",
    "On a normal locally Noetherian scheme, an actual Cartier presentation is effective exactly when all actual Weil coefficients are nonnegative.",
    "DVR regularity, affine codimension-one extension and regular equations in actual stalks are proved. Effectivity is an output rather than a geometric bridge input.",
    [
      "An actual integral locally Noetherian scheme with integrally closed stalks.",
      "Actual Cartier presentations and their constructed Weil cycles."
    ],
    [
      [
        "DVR regularity",
        "Nonnegative fraction order is equivalent to divisibility of numerator by denominator."
      ],
      [
        "Actual affine extension",
        "Apply normal-domain extension to an actual affine coordinate ring and its actual scheme stalks."
      ],
      [
        "Effectivity equivalence",
        "Extend all equations to actual local rings; the converse follows from nonnegative DVR orders."
      ]
    ]
  ],
  "geomsupport": [
    "Actual Cartier support and real-sum pullback",
    "Full Cartier support is the closure of the nonzero actual Weil primes. Effective real sums have the union of positive-weight supports; the constructed decomposition has inverse-image pullback support.",
    "Actual unit neighborhoods, closed support, codimension-one closure, positive real sums and pullback of the constructed decomposition are proved. Compatibility with termwise pullback of the original R-Cartier presentation and the upstairs fiber dichotomy remain open.",
    [
      "Actual integral normal locally Noetherian schemes and a dominant morphism.",
      "Arbitrary original real weights with effective actual Weil sum; decomposition requires a quasi-compact base."
    ],
    [
      [
        "Full support",
        "Extend local units to unit sections and extend both an equation and its inverse from zero height-one orders."
      ],
      [
        "Positive-weight union",
        "Effective Cartier coefficients do not cancel; closure commutes with finite unions."
      ],
      [
        "Actual pullback",
        "Construct effective Cartier pullbacks and use reflection of local units to prove inverse-image support."
      ],
      [
        "Arbitrary real presentation",
        "Construct an effective Cartier decomposition and pull it back. Compatibility with the original termwise pullback and the upstairs dichotomy remain open."
      ]
    ]
  ]
});

entries.rdecomp[0]='Actual R-Cartier: effective Cartier decomposition';
entries.rdecomp[1]='An effective actual real Weil combination has a constructed nonnegative real decomposition into actual effective Cartier presentations, preserving the weighted Weil cycle and every original zero coefficient.';
entries.rdecomp[2]='Rational-cone decomposition, integral combinations, actual Weil coefficients and regular Cartier equations are proved. The equality is an equality of constructed actual Weil cycles. The full negativity lemma remains open.';
entries.rdecomp[4][3]=['Actual Cartier effectivity: proved','Apply proved codimension-one extension to turn nonnegative Weil coefficients into regular local equations.'];
entries.fiberdown[2]='Actual Cartier effectivity, full support of effective real sums and support pullback of the constructed decomposition are proved. Compatibility with original termwise pullback and the upstairs fiber dichotomy remain open. The complete theorem is not proved.';
entries.fiberdown[3][1]='Verified: actual effective Cartier decomposition, geometric support closure and support pullback of the decomposition. Open: compatibility with the original termwise pullback.';
entries.fiberdown[4][2]=['Effective R-Cartier decomposition: verified','Every constructed Cartier equation is regular in the actual stalks, and the actual Weil cycle identity is proved.'];
entries.fiberdown[4][3]=['Full support pullback of the decomposition: verified','Identify support with the closure of nonzero Weil primes, then prove inverse-image support for its constructed pullback.'];
entries.fiberdown[4].push(['Still to connect','Prove compatibility with original termwise pullback and complete the upstairs fiber dichotomy.']);
entries.chow[2]='Actual R-Cartier push-pull, effective Cartier decomposition, full support identification and support pullback of the decomposition are proved. Finite-cover projectivity, finite normalization, global curve intersections, original termwise-pullback compatibility and the upstairs fiber dichotomy remain open.';

// Actual original-presentation pullback: formal-18
entries.geomsupport[1]='Original real weights may be negative. If the actual real Weil sum is effective, its original termwise Cartier pullback is effective and has exactly inverse-image full support.';
entries.geomsupport[2]='Compatibility between original termwise pullback and effective-decomposition pullback is proved, including exceptional divisors above higher-codimension centers. Actual effectivity, support closure and inverse-image support are complete. The upstairs fiber dichotomy is not proved.';
entries.geomsupport[4][3]=['Original termwise pullback: verified','Retain original coefficient coordinates and products of actual equations. Pull back actual local units and compute source DVR orders to prove equality of the actual pulled-back Weil cycles.'];
entries.geomsupport[4].push(['Exceptional coefficients','The target point need not have codimension one: pull back units in its actual stalk, then compute orders at source codimension-one points.']);
entries.rdecomp[2]='Actual effective Cartier decomposition and preservation of original zero coefficients are proved. The stronger version also retains original coefficient coordinates and products of actual local equations, allowing comparison with original termwise pullback. The full negativity lemma remains open.';
entries.fiberdown=[
 'Actual R-Cartier fiber-support descent',
 'For a proper birational modification, the actual original termwise pullback of an effective R-Cartier presentation is effective, and the fiber-support dichotomy is equivalent upstairs and downstairs.',
 'Actual scheme surjectivity, original termwise pullback, effectivity, full inverse-image support and dichotomy descent equivalence are proved. This node does not prove that the upstairs dichotomy holds. The complete theorem is not proved.',
 ['Actual normal integral locally Noetherian schemes, a quasi-compact target and a proper birational modification.','An actual finite R-Cartier presentation with arbitrary real weights and effective actual real Weil sum.','The output is equivalence of upstairs and downstairs alternatives. The upstairs alternative still needs a separate geometric proof.'],
 [
  ['Construct original pullback','Construct each actual Cartier pullback and retain its actual local equations.'],
  ['Compare effective decomposition','Use original coordinates and products of local equations to prove equality of the two actual pulled-back Weil cycles.'],
  ['Full inverse-image support','Actual effectivity and inverse-image support in all codimensions are proved rather than assumed.'],
  ['Actual descent','Proper birational surjectivity reflects disjointness and containment, proving equivalence of both alternatives.'],
  ['Separate remaining problem','The geometric proof that the upstairs alternative always holds remains open. This node proves only descent equivalence.']
 ]
];
entries.chow[2]='Actual R-Cartier push-pull, effective decomposition, effectivity and full support of original termwise pullback, and dichotomy descent equivalence are proved. Finite-cover projectivity, finite normalization, global curve intersections and the upstairs fiber dichotomy remain open.';
