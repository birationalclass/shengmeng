module

/-
Third-party source: Vilin97/Autoformalization, Apache-2.0.
Pinned upstream commit: 09497ebf6ee48ef49c4f3d24501954bc3a2855d6.
Original path: coherent-cohomology-finite/CoherentCohomologyFinite/ProjectiveLaurentCechCategoricalFiniteTransport.lean
Local adaptation: imports relocated to Negativity.External.Laurent.
-/
public import Negativity.External.Laurent.ProjectiveLaurentCechShortComplexFiniteness

@[expose] public section

/-!
# Transporting Laurent Čech finiteness to categorical homology

The explicit quotient, its lifted finiteness witness, and its
categorical comparison have each been checked in preceding modules.
This final layer only transports finite generation across that compiled
linear equivalence.
-/

set_option autoImplicit false

namespace LeanEval.AlgebraicGeometry.ProjectiveLaurentCech

variable {ι R : Type*} [Fintype ι] [LinearOrder ι]

/-- Positive categorical Laurent Čech homology is finite over a
Noetherian coefficient ring. -/
theorem laurentCechPositiveCategoricalHomologyFinite
    [CommRing R] [IsNoetherianRing R]
    (d : ℤ) (q : ℕ) :
    Module.Finite R
      ((laurentCechComplex
        (ι := ι) (R := R) d).homology (q + 1)) :=
  moduleFiniteOfLinearEquiv
    (laurentCechShortComplexPositiveHomology_finite
      (ι := ι) (R := R) d q)
    (laurentCechHomologyShortComplexLinearEquiv
      (ι := ι) (R := R) d q).symm

end LeanEval.AlgebraicGeometry.ProjectiveLaurentCech
