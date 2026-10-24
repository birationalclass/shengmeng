module
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
universe u

/-- Passing from an actual domain to its actual fraction field preserves
the transcendence degree over the original coefficient field. -/
theorem fraction_field_trdeg
    (k A F : Type u) [Field k] [CommRing A] [IsDomain A] [Field F]
    [Algebra k A] [Algebra A F] [Algebra k F] [IsScalarTower k A F]
    [IsFractionRing A F] : Algebra.trdeg k F = Algebra.trdeg k A := by
  letI : FaithfulSMul A F :=
    (faithfulSMul_iff_algebraMap_injective A F).mpr (IsFractionRing.injective A F)
  letI : Algebra.IsAlgebraic A F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := F) (C := F)).mpr inferInstance
  simpa [trdeg_eq_zero] using (trdeg_add_eq k A (A := F)).symm

/-- The actual rational function field increases the original coefficient
field's transcendence degree by precisely one. -/
theorem rational_function_trdeg
    (k E : Type u) [Field k] [Field E] [Algebra k E] :
    Algebra.trdeg k (RatFunc E) = Algebra.trdeg k E + 1 := by
  have hfrac := fraction_field_trdeg E (Polynomial E) (RatFunc E)
  rw [Polynomial.trdeg_of_isDomain] at hfrac
  have h := trdeg_add_eq k E (A := RatFunc E)
  rw [hfrac] at h
  exact h.symm

end LinearStudy
