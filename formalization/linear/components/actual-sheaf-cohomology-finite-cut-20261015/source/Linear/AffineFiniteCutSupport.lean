module
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
universe u v

/-- SAME actual original cut V(I) has finite underlying support if its
ORIGINAL quotient coordinate ring is finite-dimensional over the field.
Reuse native Artinian/finiteness and actual quotient comap image formula. -/
theorem affineClosedCut_zeroLocus_finite_of_fieldFinite
    (k : Type v) [Field k] (R : Type u) [CommRing R] [Algebra k R]
    (I : Ideal R) [Module.Finite k (R ⧸ I)] :
    (PrimeSpectrum.zeroLocus (I : Set R)).Finite := by
  letI : IsArtinianRing (R ⧸ I) := IsArtinianRing.of_finite k (R ⧸ I)
  have hfin := Set.finite_range (PrimeSpectrum.comap (Ideal.Quotient.mk I))
  rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,Ideal.mk_ker] at hfin
  exact hfin

end LinearStudy
