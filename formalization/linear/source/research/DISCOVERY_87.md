# Library discovery and precise correspondence for checkpoint 87

Pinned Lean 4.35.0-rc3 and mathlib 2a885768dae569d938bb9ff3474da6a8753bb90a.

Primary online discovery and pinned sources inspected:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/NoetherNormalization.html
  — actual finite injective normalization, `exists_finite_inj_algHom_of_fg`.
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/KrullDimension/Polynomial.html
  — dimension of an actual multivariable polynomial ring over a field.
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/HasGoingUp.html
  and pinned Ideal/GoingUp.lean — lying-over, lifted finite prime chains and
  strict contraction for integral extensions.
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/MvPolynomial/Basic.html
  and Degrees.html — polynomial induction, actual bounded supports and degrees.
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/AlgebraicIndependent/TranscendenceBasis.html
  — `trdeg_add_eq`, actual normalization-variable transcendence degree,
  `AlgEquiv.trdeg_eq` and polynomial transcendence degree.
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Localization/Integral.html
  — algebraicity over a domain and its actual fraction field.
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Spectrum/Prime/Topology.html
  — actual spectrum topological dimension equals ring Krull dimension.

Also inspected pinned MvPolynomial/RingTheory, Module.Finite generators,
finite-dimensional basis/cardinality formulas, polynomial degree and limit
comparison, existing user HomogeneousCoordinateFiltration and original
cone/ratio/chart function-field isomorphisms. Focused searches did not locate
a direct compatible Hilbert-polynomial/Krull-dimension theorem. That missing
comparison is developed from the reusable normalization and dimension code.

The actual proof route:

1. Lift actual prime-ideal chains under an injective integral extension.
   This proves preservation of Krull dimension.
2. Apply mathlib actual Noether normalization; its number of variables is
   proved equal to the original ring's actual Krull dimension.
3. Construct representatives for the normalizing variables, finite module
   generators and multiplication matrices. Their actual coefficient degrees
   give two bounds for the ORIGINAL total-degree coordinate filtration.
4. Bound polynomial coefficient spaces by actual monomial bases and a bounded
   coefficient linear map. Compare eventual original Hilbert growth with
   powers of N using proved polynomial asymptotics.
5. Conclude actual cumulative Hilbert polynomial degree = original ring Krull
   dimension. In the original projective cone this is deg(P)+1.
6. Actual finite normalization also computes actual transcendence degree.
   Actual fraction fields preserve it, and actual E(t) increases it by one.
   The previously constructed original cone/chart/ratio field isomorphisms
   therefore identify the ORIGINAL inhabited affine chart dimension with
   deg(P), including its actual affine spectrum's topological dimension.
7. Connect that SAME dimension to the original chart degree and EVERY original
   iterate's WHOLE general fiber point count: D=q^r and card=(q^k)^r.

No precomputed dimension, cardinality, degree formula, matrix degree bound
or normalization map is encoded as a conclusion input. The chart point
explicitly ensures the chart is inhabited. This computes the actual affine
chart's dimension; global Proj/Scheme comparison is a separate obligation.

Current-paper correspondence: this advances Setup 1.4 and the main proof's
fiber degree input. It does not prove Bertini selection, original global
relation assembly, canonical-sheaf/Koszul/proper-duality/Serre lifting, actual
Cartier/Bezout intersection or the final Linearity Theorem. Private and public
compiler logs, exact kernel types and axiom audits determine verification.
