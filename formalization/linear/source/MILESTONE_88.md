# Checkpoint 88: one actual dimension for whole fibers and local parameters

The complete original Linearity Theorem remains unproved.

Three new modules and seven theorem proofs establish:

- The actual Krull dimension of a finite-type characteristic-zero domain equals
  the rank of its actual Kähler differential module. No global smoothness is
  assumed. The proof constructs the normalization/fraction-field scalar tower,
  separable extension and transported differential basis.
- For the original inhabited prime projective chart, this differential rank,
  the actual chart Krull dimension and its Hilbert polynomial degree agree.
- At every smooth original chart point, construct polynomial local parameters
  with exactly that cardinality. The same integer also computes every original
  iterate's whole general fiber cardinality as (q^k)^r.

These statements do not assume a dimension, rank or fiber-cardinality formula.
The constructed local parameters may be nonlinear polynomials; common linear
coordinates and all local normal equations on the same complete original
Setup fiber still require assembly before Section 3 can be marked complete.

Current manuscript Section 2 Lemma 2.1 is complete. Section 1 Setup and Section 3
local geometry have advanced. Global Proj/Scheme comparison, Bertini, the complete
original homogeneous relation, Section 4 canonical-sheaf/Koszul/proper-duality/
uniform-Serre lifting, actual Cartier/Bézout inequality and the final theorem
remain open.

Evidence: snapshot.json, full-audit.json, research/build-checkpoint88.log,
research/audit-checkpoint88.log, research/checkpoint88-private-provenance.json
and research/DISCOVERY_88.md. All changed modules and the aggregate project
compiled successfully; the full declaration audit uses only standard Lean
axioms, with no sorryAx or project axiom.
