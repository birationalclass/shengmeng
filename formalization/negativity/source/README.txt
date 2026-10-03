Actual proper negativity lemma — both conclusions

Final theorem: Negativity.actual_proper_negativity_lemma
Source: Negativity/ActualProperNegativityComplete.lean

Let k be algebraically closed of arbitrary characteristic. For a proper
birational morphism f:X->Y of normal k-varieties and a real Cartier divisor D
with -D relatively nef, the final theorem proves:
  (1) D is effective if and only if the actual Weil pushforward f_*D is effective.
  (2) If D is effective, every fiber is disjoint from Supp D or contained in it.

The code uses actual mathlib schemes, finite Cartier presentations, actual
Weil cycles, and intersection by local orders on curve normalizations.
The final theorem has no formal-functions, curve-existence, projection-formula,
Chow-modification, numerical-positivity, or cohomology-finiteness input.

Actual proper cohomology finite generation is reused from pinned AINTLIB
source and rebuilt on this project's toolchain. The actual relative Rees
image and its native Cech cohomology are identified with the source's summed
ideal-power H1, including genuine restrictions, scalars, and boundaries.
Finite generation supplies a uniform kernel bound. A clopen characteristic
function extends to finite thickenings and then lifts to actual global
sections. Normal proper birational function descent makes its fiber
restriction constant, proving actual closed-fiber connectedness. The
all-fiber support argument and independent effectivity proof complete the
two-part theorem. A separate closed-fiber formal-functions comparison for
proper normal birational morphisms is also proved; the final connectedness
route uses finite characteristic lifts.

Some auxiliary results have general explicit hypotheses or abstract model
parameters. Their statements remain visible. They are distinct from the
final actual geometric theorem, whose required geometric bridges are proved.

Verification: local lake build and #print axioms. Every exported own theorem
is checked against the whitelist propext, Classical.choice, Quot.sound.
No sorry, admit, added axiom, or sorryAx is accepted. Browser rendering and
the curated mathematical graph are not independent Lean verification.

Reproduce with Lean's elan and Git:
  lake update
  lake exe cache get
  lake build
  lake env lean CheckAxioms.lean

lean-toolchain, lakefile.toml, and lake-manifest.json pin the toolchain and
dependencies. The archive deliberately excludes .lake and local user data.
The complete selected third-party source closures, Apache-2.0 licenses,
revision/hash provenance, and migration notes are in External/Laurent and
External/Aintlib. Imported source authors and copyright notices are retained.
The private Hartshorne scan is not included.

The exact audited own declarations, source positions, hashes, and checking
time are recorded in snapshot.json and verification.txt. The dependency
atlas is a curated mathematical blueprint, not a kernel dependency dump.
