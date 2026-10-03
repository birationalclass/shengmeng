module

/-
Third-party source: Vilin97/Autoformalization, Apache-2.0.
Pinned upstream commit: 09497ebf6ee48ef49c4f3d24501954bc3a2855d6.
Original path: coherent-cohomology-finite/CoherentCohomologyFinite/ProjectiveLaurentCechRawShortComplexFiniteness.lean
Local adaptation: imports relocated to Negativity.External.Laurent.
-/
public import Negativity.External.Laurent.ProjectiveLaurentCechRawShortComplex

@[expose] public section

/-!
# Finiteness of the raw Laurent Čech short-complex homology

The raw three-term complex exposes the same cochain types used by the
explicit exponent calculation.  Thus its left homology can receive the
kernel-modulo-boundary finiteness theorem without a large dependent
carrier conversion.
-/

set_option autoImplicit false

namespace LeanEval.AlgebraicGeometry.ProjectiveLaurentCech

variable {ι R : Type*} [Fintype ι] [LinearOrder ι]

attribute [local instance 2000] laurentCechCyclesAddCommGroup

/--
The explicit positive quotient stated using the exact `ModuleCat.ofHom`
carrier expressions used by the raw short complex.
-/
theorem laurentCechPositiveModuleCarrierCohomology_finite
    [CommRing R] [IsNoetherianRing R]
    (d : ℤ) (q : ℕ) :
    Module.Finite R
      ((ModuleCat.ofHom
          (differential
            (ι := ι) (R := R) d (q + 1))).hom.ker ⧸
        Submodule.comap
          (ModuleCat.ofHom
            (differential
              (ι := ι) (R := R) d (q + 1))).hom.ker.subtype
          (ModuleCat.ofHom
            (differential
              (ι := ι) (R := R) d q)).hom.range) :=
  laurentCechPositiveCohomology_finite
    (ι := ι) (R := R) d q

/-- Positive left homology of the raw Laurent Čech short complex is
finite over a Noetherian coefficient ring. -/
theorem laurentCechRawShortComplexHomology_finite
    [CommRing R] [IsNoetherianRing R]
    (d : ℤ) (q : ℕ) :
    Module.Finite R
      ((laurentCechRawShortComplex
        (ι := ι) (R := R) d q).moduleCatLeftHomologyData.H) :=
  shortComplexHomologyFiniteOfEqSubmodule
    (laurentCechRawShortComplex (ι := ι) (R := R) d q)
    (ModuleCat.ofHom
      (differential (ι := ι) (R := R) d q)).hom
    (ModuleCat.ofHom
      (differential (ι := ι) (R := R) d (q + 1))).hom
    rfl
    rfl
    (Submodule.comap
      (ModuleCat.ofHom
        (differential
          (ι := ι) (R := R) d (q + 1))).hom.ker.subtype
      (ModuleCat.ofHom
        (differential
          (ι := ι) (R := R) d q)).hom.range)
    rfl
    (laurentCechPositiveModuleCarrierCohomology_finite
      (ι := ι) (R := R) d q)

end LeanEval.AlgebraicGeometry.ProjectiveLaurentCech
