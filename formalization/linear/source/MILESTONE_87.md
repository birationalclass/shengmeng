# Checkpoint 87: actual Hilbert degree, chart dimension and whole fibers

This is checked partial progress toward the original Linearity Theorem.
The final theorem remains unproved.

Starting with the actual original homogeneous map f, totally invariant
homogeneous prime V and an inhabited standard chart, the new proofs establish:

- Integral injective extensions preserve actual ring Krull dimension.
- An actual finite Noether normalization computes both the original domain's
  Krull dimension and transcendence degree.
- Its original coordinate filtration is bounded above using constructed module
  generators, multiplication matrices and coefficient degrees; injectivity gives
  the lower bound. These are proved growth bounds, not supplied inputs.
- The original cumulative Hilbert polynomial degree equals the original cone
  ring Krull dimension.
- The actual cone, chart and ratio fraction fields and transcendence-degree
  towers give P.natDegree = r, where r is the actual original affine chart ring
  Krull dimension, also the dimension of its actual prime spectrum.
- The WHOLE original chart pullback degree is q^r. For EVERY original iterate k,
  construct a nonempty target open where EVERY WHOLE point fiber is finite and
  has (q^k)^r points, with the same actual chart dimension r.

The aggregate original-map statements do not assume dimension, cardinality,
degree, normalization or growth formulas as conclusions supplied by the caller.

Still OPEN: the global projective Proj/Scheme comparison, the connection of this
actual dimension with the differential rank used by the local parameter models,
Bertini selection, assembly of the full original projective polynomial relation,
canonical-sheaf fixed-twist injection, geometric Koszul/proper duality/uniform
Serre lifting, and the actual Cartier/Bezout intersection inequality.

The historical Lean lemma31_complete corresponds to CURRENT manuscript Lemma
2.1 and is already proved. Checkpoint 87 advances Section 1 Setup, not the full
Section 3 relation or Section 4 lifting lemma.

Evidence: snapshot.json, full-audit.json, build.log,
research/checkpoint87-private-provenance.json and research/DISCOVERY_87.md.
