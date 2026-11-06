module
public import Linear.FiniteTypeFieldEndomorphism
public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.RingHom.Finite
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy

/-- Finite image extension transported to the actual endomorphism. -/
theorem fieldEndomorphism_finite
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.EssFiniteType K L]
    (φ : L →ₐ[K] L) : φ.toRingHom.Finite := by
  letI : Module.Finite φ.fieldRange L := fieldEndomorphism_range_finite φ
  have hf : (algebraMap φ.fieldRange L).Finite := RingHom.finite_algebraMap.mpr inferInstance
  have he : φ.equivFieldRange.toRingHom.Finite :=
    RingHom.Finite.of_surjective _ φ.equivFieldRange.surjective
  have hc := hf.comp he
  have h : (algebraMap φ.fieldRange L).comp φ.equivFieldRange.toRingHom = φ.toRingHom := by
    ext x
    rfl
  rw [h] at hc
  exact hc

/-- Generic nonramification is a property of the actual map, not only
of an independently supplied image-field extension. -/
theorem fieldEndomorphism_formallyUnramified
    {K L : Type*} [Field K] [Field L] [CharZero L] [Algebra K L] [FinTrdeg K L]
    (φ : L →ₐ[K] L) : φ.toRingHom.FormallyUnramified := by
  letI : Algebra.FormallyUnramified φ.fieldRange L :=
    fieldEndomorphism_range_formallyUnramified φ
  have hf : (algebraMap φ.fieldRange L).FormallyUnramified :=
    RingHom.formallyUnramified_algebraMap.mpr inferInstance
  have he : φ.equivFieldRange.toRingHom.FormallyUnramified :=
    RingHom.FormallyUnramified.of_surjective φ.equivFieldRange.surjective
  have hc := he.comp hf
  have h : (algebraMap φ.fieldRange L).comp φ.equivFieldRange.toRingHom = φ.toRingHom := by
    ext x
    rfl
  rw [h] at hc
  exact hc

end LinearStudy
