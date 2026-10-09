module
public import Linear.NativeDualDegreeZeroSpanValues
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
namespace LinearStudy
open CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable [Module.Finite R S]
attribute [local instance] coextensionGradedBaseModule
attribute [local instance] nativeCoextensionNormalizationBaseModule
attribute [local instance] LocalizedModule.moduleOfIsLocalization
attribute [local instance] nativeHomogeneousAwayModuleScalar

/-- Actual localized native-dual evaluation is bilinear over the actual
degree-zero base chart ring, with its native chart scalar actions. -/
def finiteNativeDualHomogeneousEvaluationMap
    (a : R) (hinj : Function.Injective (algebraMap R (Localization.Away a))) :
    let D := (ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))
    LocalizedModule (Submonoid.powers a) D →ₗ[HomogeneousLocalization.Away 𝒜 a]
      (LocalizedModule (Submonoid.powers a) S →ₗ[HomogeneousLocalization.Away 𝒜 a]
        Localization.Away a) := by
  dsimp only
  let P := Submonoid.powers a
  let Q := Localization.Away a
  let A₀ := HomogeneousLocalization.Away 𝒜 a
  let D := (ModuleCat.restrictScalars (algebraMap R S)).obj
    ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))
  letI : Module Q (LocalizedModule P S) := LocalizedModule.moduleOfIsLocalization
  letI : Module Q (LocalizedModule P D) := LocalizedModule.moduleOfIsLocalization
  let E := finiteNativeCoextensionLocalizationEquiv (S := S) (Q := Q) P hinj
  exact {
    toFun := fun ell => {
      toFun := E ell
      map_add' := (E ell).map_add
      map_smul' := by
        intro c x
        change (E ell) (algebraMap A₀ Q c • x) = algebraMap A₀ Q c • (E ell) x
        rw [← localizedModule_abstract_smul_eq_native P]
        exact (E ell).map_smul (algebraMap A₀ Q c) x }
    map_add' := by
      intro ell₁ ell₂
      ext x
      exact LinearMap.congr_fun (E.map_add ell₁ ell₂) x
    map_smul' := by
      intro c ell
      ext x
      change (E (algebraMap A₀ Q c • ell)) x = algebraMap A₀ Q c • (E ell) x
      rw [← localizedModule_abstract_smul_eq_native P]
      exact LinearMap.congr_fun (E.map_smul (algebraMap A₀ Q c) ell) x }

theorem finiteNativeDualHomogeneousEvaluationMap_apply
    (a : R) (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (ell : LocalizedModule (Submonoid.powers a)
      ((ModuleCat.restrictScalars (algebraMap R S)).obj
        ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))))
    (x : LocalizedModule (Submonoid.powers a) S) :
    finiteNativeDualHomogeneousEvaluationMap 𝒜 a hinj ell x =
      finiteNativeCoextensionLocalizationEquiv (Q := Localization.Away a)
        (Submonoid.powers a) hinj ell x := rfl

end LinearStudy
