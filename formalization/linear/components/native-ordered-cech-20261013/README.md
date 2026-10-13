# Original Lemma4.2: actual native ordered Cech foundation

Original Lemmas4.1/4.2 and the main Linearity Theorem remain OPEN.
The canonical/normalized-dualizing identification remains UNVERIFIED.
One fixed bound before all original iterates has not been proved.

This component constructs actual base-linear section presheaves and actual
ordered Cech complexes. The differential is the alternating sum of original
open restrictions, and d squared equals zero. Maps of actual module sheaves
induce natural maps of these actual complexes.

Let K be a field, S a graded commutative K-algebra, X=Proj(S), and a_i in S_1.
Then each actual finite Cech intersection of D_+(a_i) equals the actual basic
open for their product, which is homogeneous of positive degree. Thus it is
affine, without a separatedness or affine-intersection certificate.

For any actual X->Y, an actual short exact sequence of quasicoherent X-modules
gives a short exact sequence of the actual base-linear ordered Cech complexes.
In particular, if 0->A->B->C->0 is such a sequence, ExactAt(q) for B and
ExactAt(q+1) for A imply ExactAt(q) for C by the actual homology exact sequence.

For the actual homogeneous graded module surjection E->F, let E be finite over
a Noetherian S, with compatible K-linear integer decompositions and scalar
towers. Assume the degree-one opens cover X. The actual module kernel and
associated sheaf map form a short exact sequence for every integer k. Actual
finite presentation of each sheaf yields their quasicoherence, so the actual
ordered Cech sequence is short exact. F is finite by the surjection; it is
not an extra finite-generation hypothesis.

The previous actual native tensor comparison induces an actual isomorphism
between the ordered Cech complexes for T_m(S) tensor T_k(M) and T_(k+m)(M).
For a finite index set, exactness above its cardinality is the induction base.
Neither result proves eventual H1 vanishing.

Minimal AINTLIB reuse also proves the support-restricted combinatorial
contraction from Stacks Tag01XT: for any commutative R, support N and i notin N,
the explicit prepend homotopy satisfies dh+hd=1. Alternating extension and
restriction prove every ordered positive-degree support cocycle is a boundary.
These are actual specified support complexes; their comparison with the native
geometric Laurent-weight Cech complex remains OPEN.

15 new LF modules, 2620 physical source lines,108 exact declarations,
76 proofs (including named instances),32 definitions. Closed source contains
174 modules; all 159 earlier dependencies match
prior frozen archives byte-for-byte. All exact types and transitive axioms
pass: only propext,Classical.choice,Quot.sound. Logs and source hashes included.
Resource controls: one compiler,8GiB Windows Job,2threads,CPU25%,20min timeout.
Whole-project checkpoint180 and full-project CI remain unchanged.

Still OPEN: actual native twist Cech to Laurent-weight comparison, positive
twist acyclicity, the uniform H1 bound, original ideal-sheaf identification,
ambient homogeneous polynomial lifting, genuine canonical identification and
the original nonzero section needed by Lemma4.1. No incomplete step is promoted.

Reproduce with the pinned lean-toolchain and lake-manifest, compiling the
included Linear modules in dependency order, then CheckAxioms.lean. Linear.lean
is a convenience import entry, not a separately accepted full-project build.
