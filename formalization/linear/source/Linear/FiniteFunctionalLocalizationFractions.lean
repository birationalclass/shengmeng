module
public import Linear.FiniteFunctionalLocalizationEquiv
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
variable (P : Submonoid R) [IsLocalization P Q]
attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- Explicit evaluation on two actual fractions. Both denominators
are accounted for, so this is usable on homogeneous chart fractions. -/
theorem finiteFunctionalLocalizationEquiv_apply_fraction
    (hinj : Function.Injective (algebraMap R Q))
    (ψ : M →ₗ[R] R) (x : M) (s t : P) :
    finiteFunctionalLocalizationEquiv P hinj (LocalizedModule.mk ψ s)
      (LocalizedModule.mk x t) = IsLocalization.mk' Q (ψ x) (s*t) := by
  let e := finiteFunctionalLocalizationEquiv (M := M) P hinj
  have hs : (s : R) • LocalizedModule.mk ψ s = LocalizedModule.mk ψ 1 := by
    simpa only [LocalizedModule.smul'_mk, Submonoid.smul_def] using
      LocalizedModule.mk_cancel s ψ
  have ht : (t : R) • LocalizedModule.mk x t = LocalizedModule.mk x 1 := by
    simpa only [LocalizedModule.smul'_mk, Submonoid.smul_def] using
      LocalizedModule.mk_cancel t x
  have hcalc : e ((s : R) • LocalizedModule.mk ψ s)
      ((t : R) • LocalizedModule.mk x t) =
        algebraMap R Q ((s : R)*(t : R)) *
          e (LocalizedModule.mk ψ s) (LocalizedModule.mk x t) := by
    have he : e ((s : R) • LocalizedModule.mk ψ s) =
        (s : R) • e (LocalizedModule.mk ψ s) := by
      simpa only [IsScalarTower.algebraMap_smul] using
        e.map_smul (algebraMap R Q (s : R)) (LocalizedModule.mk ψ s)
    have hf : e (LocalizedModule.mk ψ s) ((t : R) • LocalizedModule.mk x t) =
        (t : R) • e (LocalizedModule.mk ψ s) (LocalizedModule.mk x t) := by
      simpa only [IsScalarTower.algebraMap_smul] using
        (e (LocalizedModule.mk ψ s)).map_smul (algebraMap R Q (t : R))
          (LocalizedModule.mk x t)
    rw [he, LinearMap.smul_apply, hf]
    simp only [Algebra.smul_def, map_mul, mul_assoc]
  have hclear : algebraMap R Q ((s : R)*(t : R)) *
      e (LocalizedModule.mk ψ s) (LocalizedModule.mk x t) = algebraMap R Q (ψ x) := by
    rw [← hcalc, hs, ht]
    exact finiteFunctionalLocalizationEquiv_apply_mk P hinj ψ x
  apply (IsLocalization.map_units Q (s*t)).mul_left_cancel
  exact hclear.trans (IsLocalization.mk'_spec' Q (ψ x) (s*t)).symm

end LinearStudy
