module
public import Linear.HomogeneousLocalizationRefinementValue
public import Linear.FiniteNativeDualRefinementEvaluation
public import Linear.NativeDualFullSourceChartEquiv
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra

/-- The actual full-source-chart dual comparison commutes with homogeneous
restriction to a common original localization, including a stalk.
Both dual and source fractions are restricted by constructed module maps. -/
theorem finiteNativeDualFullSourceChartMap_refinement_value
    (a : R) (ha : a ∈ 𝒜 1) (T : Submonoid R)
    (hPT : Submonoid.powers a ≤ T)
    (hinja : Function.Injective (algebraMap R (Localization.Away a)))
    (hinjT : Function.Injective (algebraMap R (Localization T)))
    (ell : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a)
    (y : HomogeneousLocalization.Away 𝓑 (algebraMap R S a)) :
    finiteNativeCoextensionLocalizationEquiv (Q := Localization T) T hinjT
      (originalLocalizedModuleRefinement (Submonoid.powers a) T hPT ell.val)
      (originalLocalizedModuleRefinement (Submonoid.powers a) T hPT
        ((nativeNormalizationSourceChartEquiv 𝒜 𝓑 a ha).symm y).val) =
      (HomogeneousLocalization.mapId 𝒜 hPT
        (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinja ell y)).val := by
  rw [finiteNativeDual_refinement_evaluation (Submonoid.powers a) T hPT hinja hinjT
      ell.val ((nativeNormalizationSourceChartEquiv 𝒜 𝓑 a ha).symm y).val,
    ← finiteNativeDualFullSourceChartMap_apply_val 𝒜 𝓑 a ha hinja,
    homogeneousLocalizationRefinement_val 𝒜 (Submonoid.powers a) T hPT]

/-- If actual original dual and source sections agree in the same
localization, the values of their chart pairings agree there as well.
This is a proved compatibility law, not an assumed comparison certificate
or a claim that the entire canonical sheaf has already been glued. -/
theorem finiteNativeDualFullSourceChartMap_common_value
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1) (T : Submonoid R)
    (hPa : Submonoid.powers a ≤ T) (hPb : Submonoid.powers b ≤ T)
    (hinja : Function.Injective (algebraMap R (Localization.Away a)))
    (hinjb : Function.Injective (algebraMap R (Localization.Away b)))
    (hinjT : Function.Injective (algebraMap R (Localization T)))
    (ellA : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a)
    (ellB : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) b)
    (yA : HomogeneousLocalization.Away 𝓑 (algebraMap R S a))
    (yB : HomogeneousLocalization.Away 𝓑 (algebraMap R S b))
    (hEll : originalLocalizedModuleRefinement (Submonoid.powers a) T hPa ellA.val =
      originalLocalizedModuleRefinement (Submonoid.powers b) T hPb ellB.val)
    (hY : originalLocalizedModuleRefinement (Submonoid.powers a) T hPa
        ((nativeNormalizationSourceChartEquiv 𝒜 𝓑 a ha).symm yA).val =
      originalLocalizedModuleRefinement (Submonoid.powers b) T hPb
        ((nativeNormalizationSourceChartEquiv 𝒜 𝓑 b hb).symm yB).val) :
    HomogeneousLocalization.mapId 𝒜 hPa
      (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinja ellA yA) =
    HomogeneousLocalization.mapId 𝒜 hPb
      (finiteNativeDualFullSourceChartMap 𝒜 𝓑 b hb hinjb ellB yB) := by
  apply HomogeneousLocalization.val_injective T
  rw [← finiteNativeDualFullSourceChartMap_refinement_value 𝒜 𝓑 a ha T hPa
      hinja hinjT ellA yA,
    ← finiteNativeDualFullSourceChartMap_refinement_value 𝒜 𝓑 b hb T hPb
      hinjb hinjT ellB yB]
  with_unfolding_all exact (congrArg₂
    (fun ell x => finiteNativeCoextensionLocalizationEquiv
      (Q := Localization T) T hinjT ell x) hEll hY)
end LinearStudy
