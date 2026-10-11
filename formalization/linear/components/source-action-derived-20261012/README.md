# Lemma4.1: source-algebra action and actual derived dual

The original Lemma4.1, Lemma4.2 and Linearity Theorem remain OPEN.
This is an independently checked component, not a new full project checkpoint.

Let f:X->Y be a scheme morphism, N an O_Y-module sheaf and U an original
open in Y. Set B_U=Gamma(f^-1 U,O_X) and
H_U=Hom_{O_U}((f_*O_X)|_U,N|_U). Then H_U is a B_U-module with
(b.h)_W(x)=h_W(b|_{f^-1 W}*x). The actual source action preserves all
original restrictions and agrees with the original O_Y scalar action
on pulled-back base functions. These properties are PROVED.

Let A->B be a commutative-ring map and I an actual injective resolution
of A. Let G=coextendScalars(A->B). Then H^0(G(I)) is isomorphic AS A
B-MODULE to Hom_A(B,A); all G(I^j) are B-injective and different choices
of I give homotopy-equivalent coextended complexes. In the original
integral projective model over C with a finite injective homogeneous
linear projection, this H^0 also admits a B-linear injection into B.
This is an ungraded AFFINE consequence, not omega_V(r+1)->O_V(m).

Remaining: prove the actual global native-dual/Hom comparison respects
the source action, then identify it with H^-r of the genuine normalized
dualizing complex. No normality, smoothness, freeness or CM assumption
is added to the original lemma. The source module definition is not
used as the definition of the canonical sheaf.

Evidence: four LF canonical modules, component import root and exact
19-declaration type/axiom audit have successful guarded local checks.
Only propext, Classical.choice and Quot.sound occur. Transitive source
dependencies are byte-identical to fully checked checkpoint180 and
use that local dependency cache. A clean uncached full-project build
and a new full-project GitHub Lean CI run are NOT claimed.

The pinned source closure, toolchain, lake manifest and CheckAxioms.lean
are included. Review manifest.json and evidence/exact-types-and-axioms.txt.
On the author's Windows machine all compiler invocations must use
lean_runner.run_file with the installed single-compiler resource guard:
8 GiB job limit, two threads, at most 25 percent CPU, 20 minute timeout.
Do not run an unprotected parallel rebuild on the user's computer.
