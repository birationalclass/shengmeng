# Milestone 6: nonzero socle generation for actual complete intersections

The full Linearity Theorem and the relative derivative-Jacobian target remain
unproved. This release contains 159 project theorem/lemma proofs, 45 project
definitions, and 294 audited declarations including separately counted ports.

New mathematics:

1. Function-indexed Koszul complexes are actual projective resolutions of
   regular-sequence quotients, with an explicitly proved augmentation.
2. For regular sequences H and x of the same positive length, H=Mx implies
   Ann((x) R/(H)) = ([det M]). The proof lifts the socle map between actual
   resolutions and compares the top coordinates of homotopic chain maps.
3. In a local Artinian quotient whose maximal ideal is the coordinate ideal,
   this determinant class is nonzero, using the proved nonzero intersection
   of every nonzero ideal with the socle.
4. Apply these results to the actual quotient K[[x_0,...,x_n]]/(H) of a
   regular zero-constant sequence over any field, with Artinian quotient.
   Construct H=Mx, prove its determinant class nonzero, and prove that it
   generates the socle as an ideal and a K-vector space.
5. With explicit finite-dimensionality over K, construct a perfect
   multiplication pairing normalized to 1 on the coefficient determinant.
   No perfect-pairing, socle-generation or determinant-nonzero input is used.

The coefficient determinant is NOT the formal derivative Jacobian by
construction. Their comparison, the actual relative closed-fiber comparison,
arbitrary-parameter Jacobian survival and global geometry remain unfinished.

Library discovery inspected the pinned projective-resolution lift/homotopy
API and the minimally adapted mathlib Koszul dependency (see milestone 5 and
vendor-provenance.json). Searches for a multivariable Jacobian/socle or trace
comparison did not find an applicable verified implementation. The pinned
Dedekind-domain different/minimal-polynomial derivative results require
integral-domain hypotheses incompatible with nilpotent Artinian complete
intersections. Failed search is not a claim of universal absence.

Reproduce with build.py followed by audit.py, or lake build and
lake env lean CheckAxioms.lean. Local root build and all-declaration axiom
audit succeeded, using only recorded standard axioms, with no sorryAx or
project axiom. Publication evidence is recorded separately in release.json
and live-validation.json after successful deployment verification.
