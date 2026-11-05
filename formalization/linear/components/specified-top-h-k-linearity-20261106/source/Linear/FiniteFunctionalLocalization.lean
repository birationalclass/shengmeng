module
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.Algebra.Module.LocalizedModule.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace LinearStudy
universe u
variable {R Q M : Type u} [CommRing R] [CommRing Q] [Algebra R Q]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Any actual functional into a localization has one denominator
clearing all of its values. The integral functional is constructed;
no freeness of the original finite module is assumed. -/
theorem finiteLinearFunctional_exists_denominator (P : Submonoid R)
    [IsLocalization P Q] (hinj : Function.Injective (algebraMap R Q))
    (φ : M →ₗ[R] Q) :
    ∃ s : P, ∃ ψ : M →ₗ[R] R,
      (Algebra.linearMap R Q).comp ψ = (s : R) • φ := by
  have hfg : (LinearMap.range φ).FG := by
    simpa only [Submodule.map_top] using
      (Module.Finite.fg_top (R := R) (M := M)).map φ
  obtain ⟨r, hr, hall⟩ := FractionalIdeal.isFractional_of_fg (S := P) hfg
  let j := Algebra.linearMap R Q
  let e : R ≃ₗ[R] LinearMap.range j := LinearEquiv.ofInjective j hinj
  let ρ : M →ₗ[R] LinearMap.range j := (r • φ).codRestrict _
    (fun x => hall (φ x) ⟨x, rfl⟩)
  let ψ : M →ₗ[R] R := e.symm.toLinearMap.comp ρ
  refine ⟨⟨r, hr⟩, ψ, ?_⟩
  ext x
  exact congrArg Subtype.val (e.apply_symm_apply (ρ x))

/-- The actual codomain-localization map on functionals is itself a
module localization. This is a finite-module theorem, not a
finite-free replacement of the original source. -/
theorem finiteLinearFunctional_compRight_isLocalizedModule (P : Submonoid R)
    [IsLocalization P Q] (hinj : Function.Injective (algebraMap R Q)) :
    IsLocalizedModule P
      (LinearMap.compRight (M := M) R (Algebra.linearMap R Q)) := by
  constructor
  · intro s
    rw [Module.End.isUnit_iff]
    change Function.Bijective (fun φ : M →ₗ[R] Q => (s : R) • φ)
    have hs : Function.Bijective (fun φ : M →ₗ[R] Q =>
      (algebraMap R Q (s : R)) • φ) :=
      (IsLocalization.map_units Q s).smul_bijective
    simpa only [IsScalarTower.algebraMap_smul] using hs
  · intro φ
    obtain ⟨s, ψ, hψ⟩ := finiteLinearFunctional_exists_denominator P hinj φ
    exact ⟨(ψ, s), hψ.symm⟩
  · intro φ ψ h
    have hφψ : φ = ψ := by
      ext x
      apply hinj
      exact LinearMap.congr_fun h x
    exact ⟨1, congrArg (fun f : M →ₗ[R] R => (1 : P) • f) hφψ⟩

end LinearStudy
