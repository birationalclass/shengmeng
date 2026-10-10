module
public import Linear.HomogeneousChartOverlapValue
public import Linear.NativeDualAwayOverlapEvaluation
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

/-- The PROVED full-source-chart dual comparison commutes with ACTUAL
homogeneous restriction of its value on D_+(a*b). Both original source
and dual fractions are restricted by their constructed module maps.
This is a restriction compatibility theorem, not yet global gluing or
an identification of the original dual with the canonical sheaf. -/
theorem finiteNativeDualFullSourceChartMap_overlap_value
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1)
    (hinja : Function.Injective (algebraMap R (Localization.Away a)))
    (hinjab : Function.Injective (algebraMap R (Localization.Away (a*b))))
    (ell : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a)
    (y : HomogeneousLocalization.Away 𝓑 (algebraMap R S a)) :
    finiteNativeCoextensionLocalizationEquiv (Q := Localization.Away (a*b))
      (Submonoid.powers (a*b)) hinjab
      (originalLocalizedModuleAwayOverlap a b ell.val)
      (originalLocalizedModuleAwayOverlap a b
        ((nativeNormalizationSourceChartEquiv 𝒜 𝓑 a ha).symm y).val) =
      (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)
        (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinja ell y)).val := by
  rw [finiteNativeDual_awayOverlap_evaluation a b hinja hinjab ell.val
      ((nativeNormalizationSourceChartEquiv 𝒜 𝓑 a ha).symm y).val,
    ← finiteNativeDualFullSourceChartMap_apply_val 𝒜 𝓑 a ha hinja,
    homogeneousChartOverlap_val 𝒜 a b ha hb]

end LinearStudy
