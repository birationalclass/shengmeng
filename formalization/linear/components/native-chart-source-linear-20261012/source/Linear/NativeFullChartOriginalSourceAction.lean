module
public import Linear.NativeDegreeZeroSourceActionValues
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
namespace LinearStudy
open CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra

/-- The SAME original full source-chart dual comparison intertwines
the ORIGINAL native source-chart action with precomposition by source
multiplication. All comparisons are the original explicit maps. -/
theorem finiteNativeDualFullSourceChartMap_original_source_action
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (b : HomogeneousLocalization.Away 𝓑 (algebraMap R S a))
    (ell : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a)
    (y : HomogeneousLocalization.Away 𝓑 (algebraMap R S a)) :
    finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinj
        ((nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm
          (b • nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha ell)) y =
      finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinj ell (y*b) := by
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
  letI := nativeLocalizedUpperAlgebra (S := S) (Submonoid.powers a)
  letI : Module (Localization.Away (algebraMap R S a))
    (LocalizedModule (Submonoid.powers (algebraMap R S a)) D) :=
      nativeLocalizedModuleScalar (Submonoid.powers (algebraMap R S a))
  apply HomogeneousLocalization.val_injective
  rw [finiteNativeDualFullSourceChartMap_apply_val,
    finiteNativeDualFullSourceChartMap_apply_val,
    nativeCoextensionBaseSourceZeroChartEquiv_symm_source_smul_val,
    nativeNormalizationSourceChartEquiv_symm_mul_val]
  exact nativeDualSourceChangedAction_eval_all a hinj b.val ell.val
    ((nativeNormalizationSourceChartEquiv 𝒜 𝓑 a ha).symm y).val

end LinearStudy
