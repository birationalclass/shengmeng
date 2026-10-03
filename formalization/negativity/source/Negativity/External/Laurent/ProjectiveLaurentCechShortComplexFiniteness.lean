module

/-
Third-party source: Vilin97/Autoformalization, Apache-2.0.
Pinned upstream commit: 09497ebf6ee48ef49c4f3d24501954bc3a2855d6.
Original path: coherent-cohomology-finite/CoherentCohomologyFinite/ProjectiveLaurentCechShortComplexFiniteness.lean
Local adaptation: imports relocated to Negativity.External.Laurent.
-/
public import Negativity.External.Laurent.ProjectiveLaurentCechRawShortComplexFiniteness

@[expose] public section

/-!
# Finiteness for the extracted Laurent Čech short complex

The raw short-complex finiteness result is transported across the
compiled isomorphism of explicit left-homology objects.
-/

set_option autoImplicit false

namespace LeanEval.AlgebraicGeometry.ProjectiveLaurentCech

variable {ι R : Type*} [Fintype ι] [LinearOrder ι]

/-- The explicit left homology of the short complex extracted from the
categorical Laurent complex is finite. -/
theorem laurentCechShortComplexPositiveHomology_finite
    [CommRing R] [IsNoetherianRing R]
    (d : ℤ) (q : ℕ) :
    Module.Finite R
      ((laurentCechShortComplex
        (ι := ι) (R := R) d q).moduleCatLeftHomologyData.H) :=
  moduleFiniteOfLinearEquiv
    (laurentCechRawShortComplexHomology_finite
      (ι := ι) (R := R) d q)
    (laurentCechShortComplexRawHomologyLinearEquiv
      (ι := ι) (R := R) d q).symm

end LeanEval.AlgebraicGeometry.ProjectiveLaurentCech
