# Actual native finite-graded vanishing and global section lifting

Original Lemmas4.1/4.2 and the main Linearity Theorem remain OPEN.
The genuine canonical/normalized-dualizing identification remains UNVERIFIED.

Let K be a field, sigma a finite nonempty ordered set, S=K[x_i|i in sigma],
and X=Proj S. Let M be a finite S-module with a direct-sum integer grading
compatible with the polynomial grading. T_N(M) is the ACTUAL native sheaf
defined by homogeneous local fractions. Its ordered Cech complex uses the
actual coordinate opens, actual intersections and actual restriction maps.

Then there exists ONE natural number B(M) such that, for EVERY N>=B(M)
and EVERY positive Cech degree q, the ACTUAL ordered Cech complex of T_N(M)
is exact at q. The bound is CONSTRUCTED, not an assumed eventual vanishing
input. A finite homogeneous shifted-free surjection is constructed; the
actual graded kernel is Noetherian and finite; the actual Cech short exact
sequence shifts degree until truncation by the finite cover. A finite maximum
gives one bound before all later N and all positive q.

For an arbitrary ordered open cover of an actual scheme, zero Cech cocycles
glue uniquely to global sections. For an actual short complex whose Cech
image is short exact, exactness at degree1 on its actual kernel gives global
section surjectivity. The proof lifts locally, subtracts a kernel coboundary,
and uses the actual sheaf gluing API. No derived-cohomology comparison or
global section surjectivity is assumed.

Let b:E->F be any degree-preserving SURJECTIVE S-linear map of actual integer-
graded modules, with E finite (thus F and the actual kernel are finite).
Then there exists B(b) such that for every N>=B(b), the ACTUAL native sheaf
map T_N(E)->T_N(F) is surjective on ACTUAL global sections. Its bound comes
from the proved eventual first-Cech exactness of the actual graded kernel.

The finite-biproduct argument and dimension-shift pattern reuse the fully
reviewed CBirkbeck/AINTLIB source at
ab1451487da02cd4483d0e2cdb2cc9e44bbbac17, EllipticCurve/
PositiveTwistCoproductCech.lean and ProjectiveSpacePositiveTwistCechVanishing.lean.
Only the argument is used; foreign pole sheaves, assumptions and comparison
certificates are not imported. Actual native shifted-free sheaf comparisons,
unique global gluing and actual global lifting are constructed here.

7 new LF modules, 738 physical source lines, 18 exact
declarations: 15 proofs (including named instances) and
3 definitions. Closed source contains 197
modules; all 190 older dependencies match earlier
immutable frozen archives byte-for-byte. Exact types and transitive axiom
checks pass with only propext, Classical.choice and Quot.sound.

One compiler, 8GiB hard Windows Job memory, two threads, CPU25%, 20min timeout.
Whole-project checkpoint180 and full-project CI status remain unchanged.

Still OPEN: identification with the ORIGINAL embedded variety's ideal sheaf,
ambient homogeneous-polynomial section comparison and original lifting,
the bound before every ORIGINAL iterate, genuine canonical identification
and original Lemma4.1's nonzero section. The derived sheaf-cohomology
comparison is not proved here; the global lifting proof bypasses that
comparison by actual Cech correction and gluing.

Reproduce with pinned lean-toolchain and lake-manifest, compiling included
Linear modules in dependency order, then CheckAxioms.lean. The convenience
Linear.lean entry is not a newly accepted whole-project checkpoint.
