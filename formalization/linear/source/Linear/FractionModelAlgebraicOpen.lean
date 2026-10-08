module
public import Linear.GenericSmoothUnramifiedOpen
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.RingHom.Finite
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

/-- Derive algebraicity of the actual ring map from its finite fraction model. -/
theorem ringHom_finite_fraction_model_isAlgebraic
    {R A K L : Type*} [CommRing R] [IsDomain R] [CommRing A]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    (φ : R →+* A) (e : A →+* L) (he : Function.Injective e)
    (χ : K →+* L) (hχ : χ.Finite)
    (hcomp : e.comp φ = χ.comp (algebraMap R K)) :
    letI : Algebra R A := φ.toAlgebra
    Algebra.IsAlgebraic R A := by
  letI : Algebra R A := φ.toAlgebra
  letI : Algebra K L := χ.toAlgebra
  letI : Algebra R L := (e.comp φ).toAlgebra
  letI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq
    (fun r => RingHom.congr_fun hcomp r)
  letI : Module.Finite K L := hχ
  letI : Algebra.IsAlgebraic R L := IsFractionRing.comap_isAlgebraic_iff.mpr
    (inferInstance : Algebra.IsAlgebraic K L)
  let E : A →ₐ[R] L := { __ := e, commutes' := fun _ => rfl }
  exact Algebra.IsAlgebraic.of_injective E he

/-- An algebraic dominant chart map lets a target open avoid the entire source
closed complement, rather than merely choosing one good source point. -/
theorem ringHom_algebraic_target_open_avoids_source_closed
    {R A : Type*} [CommRing R] [CommRing A] [IsDomain A]
    (φ : R →+* A)
    (halg : letI : Algebra R A := φ.toAlgebra; Algebra.IsAlgebraic R A)
    (a : A) (ha : a ≠ 0) :
    ∃ b : R, b ≠ 0 ∧ ∀ P : PrimeSpectrum A, φ b ∉ P.asIdeal → a ∉ P.asIdeal := by
  letI : Algebra R A := φ.toAlgebra
  letI : Algebra.IsAlgebraic R A := halg
  obtain ⟨b, hb, hdvd⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := R) a).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero ha)
  refine ⟨b, hb, ?_⟩
  intro P hPb hPa
  exact hPb (P.asIdeal.mem_of_dvd hdvd hPa)

end LinearStudy
