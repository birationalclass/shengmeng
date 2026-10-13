# Actual original homogeneous polynomial sections and uniform lifting

Original Lemmas4.1/4.2 and the main Linearity Theorem remain OPEN.
The genuine canonical/normalized-dualizing identification remains UNVERIFIED.

Let K be a field, sigma a finite nonempty ordered set and S=K[x_i|i in sigma].
Let X=Proj S and m>=0. T_m(S) is the ACTUAL native homogeneous-fraction
twist sheaf on the ORIGINAL Proj, with actual prime-localized values.

Then the original degree-m homogeneous polynomial map S_m -> Gamma(X,T_m(S))
is SURJECTIVE. This theorem does NOT assume global polynomial correspondence.
Proof: pass to the actual coordinate-cover zero Cech cocycle and its actual
Laurent-weight complex. Every active global weight has no negative exponent,
and its coefficient is constant across charts. Its natural exponent vector
has degree EXACTLY m. Its original monomial section has the proved actual
chart Laurent expansion. Assemble the finitely many active weights, then use
the proved injectivity of actual global-section restriction on the cover.
The theorem states surjectivity; no additional global isomorphism is claimed.

Let b:S->F be a homogeneous surjective S-linear map, where F has an actual
compatible direct-sum integer grading. Then there is ONE natural bound B(b)
before ALL N>=B(b) and ALL actual global sections s of T_N(F), such that s is
the actual sheaf image of a homogeneous polynomial Q in S_N. The uniform
global lifting bound is constructed from the actual Noetherian graded kernel
using previously audited actual Cech correction and unique sheaf gluing.
No H1 vanishing certificate or polynomial-lifting input is assumed.

For ANY original homogeneous ideal I of S, its ACTUAL quotient grading and
integer decomposition, scalar compatibility and original quotient map are
constructed. Thus the associated quotient module on the ORIGINAL ambient
Proj has the same uniform polynomial-lifting theorem. Moreover its section
is the original class [Q]/1 at every original ambient prime, as proved by
localizing the original quotient linear map. No prime, normal, smooth or
Cohen--Macaulay restriction is imposed on I or S/I.

This result concerns the quotient MODULE sheaf on the AMBIENT Proj. The
remaining comparison with the quotient Proj's own structure twist is NOT
assumed or declared proved. Original Lemma4.2 therefore remains OPEN, as do
the original canonical identification and Koszul/proper-duality nonzero
section of Lemma4.1. Derived sheaf-cohomology comparison is not proved here;
actual global lifting bypasses it with actual Cech correction and gluing.

15 new LF modules, 931 physical source lines and 34 exact
declarations: 26 theorem proofs and 8
definitions, including three local classical DecidableEq instances. These
data-valued instances are counted as definitions, never as theorem proofs.
Closed source contains 213 modules; all 198
older dependencies match earlier immutable frozen archives byte-for-byte.
Exact types and transitive axioms pass with only propext, Classical.choice
and Quot.sound; no unfinished proof or additional custom logical input.

Proof-pattern reuse in older dependencies is retained with its existing
Apache2.0 CBirkbeck/AINTLIB and mathlib attribution. The actual original
global Laurent-to-polynomial assembly and quotient fraction comparison are
constructed here against the unchanged pinned Lean/mathlib revisions.

One compiler, 8GiB Windows Job hard memory, two threads, CPU25%, 20min timeout.
Whole-project checkpoint180 and full-project CI status remain unchanged.
Reproduce with pinned lean-toolchain and lake-manifest: compile the included
Linear modules in dependency order, then CheckAxioms.lean. The convenience
Linear.lean entry is not a newly accepted whole-project checkpoint.
