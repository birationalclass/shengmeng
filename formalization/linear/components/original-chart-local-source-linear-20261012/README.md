# Lemma4.1: the original chart map is locally source linear

Original Lemmas4.1/4.2 and the main Linearity Theorem remain OPEN.
This is an independently audited component, not a full-project checkpoint.

Let V be the ORIGINAL integral projective equations over C, and let
f:Proj B -> Proj A be the SAME finite injective homogeneous linear
projection, A=C[x_0,...,x_r], B=the original homogeneous coordinate ring.
Let M be the original native coextension module sheaf, and C_i the SAME
original native-dual/Hom affine-chart morphism on the i-th coordinate
chart j_i:Spec A_i -> Proj A. The native dual is NOT defined to be omega.

Then, for EVERY coordinate i, EVERY open W in Spec A_i, EVERY ACTUAL
source function b on f^-1(j_i(W)), and EVERY original local pushforward
section t, C_i,W(b*t)=b*C_i,W(t). The source action on Hom is the actual
precomposition by source multiplication. The SAME morphism, sections,
restriction maps and source-ring actions are retained.

Localization injectivity, native-dual quasicoherence and the actual
chart-section bijection are DERIVED for the original V. Source-algebra
and source-module chart QC, top source compatibility and the original
chart sections formula are DERIVED; no local compatibility/QC certificate
is added. No normal, smooth, free or Cohen-Macaulay hypothesis is added.
The theorem retains the chosen finite injective homogeneous projection;
its prior construction is not repeated in this component. No target QC
or surjective restriction is needed for the local source-linearity proof.

The proof uses mathlib's affine QC morphism/tilde tools and the preceding
all-open source-linearity bridge. Identity scalar recovery is verified,
including its inverse. Standard chart QC and source transport are proved
separately to reduce kernel expansion. The SAME original chart morphism
is used through its already proved sections formula; it is not replaced
by a newly selected map or by an opaque agreement hypothesis.

An original base-module morphism satisfying its actual proved local
source relation is lifted to an actual source-module sheaf morphism.
All components and base scalar recovery are the SAME original morphism.
The affine version DERIVES the local relation from top source compatibility
and source-algebra/source-module QC; the target need not be QC.

Fifteen new canonical LF modules are freshly compiled serially: 22
proofs, 4 definitions, 26 exact types/axioms audited. Only propext,
Classical.choice and Quot.sound occur. Other closed project dependencies
match checkpoint180 or seven independently audited published components.
Matching caches are reused; Linear.lean is an import entry, not separately
compiled. The closed source, pinned toolchain, resource/compile logs and
exact audit are archived. One compiler, 8 GiB hard Job limit, 2 threads,
25% CPU, 20-minute timeout. Held large bundled/constructor/weighted-overlap
experiments are excluded and were never counted as verified.

Remaining: construct/verify the inverse and whole global source-linear
sheaf isomorphism; identify genuine normalized-dualizing H^-r and the
canonical twist. The manuscript then uses global generation of
Hom(omega_V(r+1),O_V)(m), a generically nonzero map and vanishing of its
torsion kernel. This component does not prove the original fixed-twist
embedding omega_V(r+1) -> O_V(m), Lemma4.1, Lemma4.2 or the main theorem.
Whole-project checkpoint180 remains unchanged.
