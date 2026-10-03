module

/-
Third-party source: Vilin97/Autoformalization, Apache-2.0.
Pinned upstream commit: 09497ebf6ee48ef49c4f3d24501954bc3a2855d6.
Original path: coherent-cohomology-finite/CoherentCohomologyFinite/ProjectiveLaurentCechCategoricalVanishing.lean
Local adaptation: imports relocated to Negativity.External.Laurent.
-/
public import Negativity.External.Laurent.ProjectiveLaurentCechCategoricalHomology
public import Negativity.External.Laurent.ProjectiveLaurentCechVanishing

@[expose] public section

/-!
# Categorical positive-twist vanishing for the Laurent Čech complex

The exponentwise contraction proves that the explicit positive-degree
Laurent Čech quotient vanishes in every nonnegative homogeneous degree.
This file transports that result to the categorical homology object of
the Laurent Čech complex.

The result is uniform over an arbitrary commutative coefficient ring.  It
is the algebraic vanishing input for relative projective acyclicity over
Noetherian affine base charts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace LeanEval.AlgebraicGeometry.ProjectiveLaurentCech

variable {ι R : Type*} [Fintype ι] [LinearOrder ι]

/--
Positive categorical Laurent Čech homology vanishes in nonnegative
homogeneous degree.
-/
theorem laurentCechPositiveCategoricalHomology_subsingleton
    [CommRing R] [Nonempty ι]
    {d : ℤ} (hd : 0 ≤ d) (q : ℕ) :
    Subsingleton
      ((laurentCechComplex
        (ι := ι) (R := R) d).homology (q + 1)) := by
  have hvanish :
      Subsingleton
        (LaurentCechPositiveCohomology
          (ι := ι) R d q) :=
    laurentCechPositiveCohomology_subsingleton
      (ι := ι) (R := R) hd q
  let e :=
    laurentCechPositiveNamedHomologyLinearEquiv
      (ι := ι) (R := R) d q
  constructor
  intro x y
  apply e.injective
  exact hvanish.elim (e x) (e y)

end LeanEval.AlgebraicGeometry.ProjectiveLaurentCech
