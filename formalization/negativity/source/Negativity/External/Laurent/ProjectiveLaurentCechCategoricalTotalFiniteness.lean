module

/-
Third-party source: Vilin97/Autoformalization, Apache-2.0.
Pinned upstream commit: 09497ebf6ee48ef49c4f3d24501954bc3a2855d6.
Original path: coherent-cohomology-finite/CoherentCohomologyFinite/ProjectiveLaurentCechCategoricalTotalFiniteness.lean
Local adaptation: imports relocated to Negativity.External.Laurent.
-/
public import Negativity.External.Laurent.ProjectiveLaurentCechCategoricalFiniteTransport

@[expose] public section

/-!
# Total finiteness of categorical Laurent Čech homology

The positive-degree categorical comparison was established separately
from the degree-zero kernel comparison.  This file combines them into
one degree-uniform theorem over a Noetherian coefficient ring.
-/

set_option autoImplicit false

namespace LeanEval.AlgebraicGeometry.ProjectiveLaurentCech

variable {ι R : Type*} [Fintype ι] [LinearOrder ι]

/-- Degree-zero categorical Laurent Čech homology is finite over a
Noetherian coefficient ring. -/
theorem laurentCechDegreeZeroCategoricalHomologyFinite
    [CommRing R] [IsNoetherianRing R]
    (d : ℤ) :
    Module.Finite R
      ((laurentCechComplex
        (ι := ι) (R := R) d).homology 0) :=
  moduleFiniteOfLinearEquiv
    (laurentCechDegreeZeroCohomology_finite
      (ι := ι) (R := R) d)
    (laurentCechDegreeZeroHomologyLinearEquiv
      (ι := ι) (R := R) d).symm

/-- Every categorical Laurent Čech homology module is finite over a
Noetherian coefficient ring. -/
theorem laurentCechCategoricalHomologyFinite
    [CommRing R] [IsNoetherianRing R]
    (d : ℤ) (n : ℕ) :
    Module.Finite R
      ((laurentCechComplex
        (ι := ι) (R := R) d).homology n) := by
  cases n with
  | zero =>
      exact
        laurentCechDegreeZeroCategoricalHomologyFinite
          (ι := ι) (R := R) d
  | succ q =>
      exact
        laurentCechPositiveCategoricalHomologyFinite
          (ι := ι) (R := R) d q

end LeanEval.AlgebraicGeometry.ProjectiveLaurentCech
