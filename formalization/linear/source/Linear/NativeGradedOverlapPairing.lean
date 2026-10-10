module
public import Linear.NativeDualGradedOverlap
public import Linear.NativeNormalizationSourceOverlap
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

/-- Restrict BOTH the actual degree-zero source module and its original
normalization dual. Their pairing is the actual homogeneous Proj
restriction of their original full-chart value. -/
theorem finiteNativeDualFullSourceChartMap_gradedOverlap_pairing
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1)
    (hinja : Function.Injective (algebraMap R (Localization.Away a)))
    (hinjab : Function.Injective (algebraMap R (Localization.Away (a*b))))
    (ell : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a)
    (y : HomogeneousLocalization.Away 𝓑 (algebraMap R S a)) :
    finiteNativeCoextensionLocalizationEquiv (Q := Localization.Away (a*b))
      (Submonoid.powers (a*b)) hinjab
      (nativeNormalizationDualOverlapMap 𝒜 𝓑 a b ha hb ell).val
      (nativeNormalizationSourceOverlapMap 𝒜 𝓑 a b ha hb
        ((nativeNormalizationSourceChartEquiv 𝒜 𝓑 a ha).symm y)).val =
      (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)
        (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinja ell y)).val := by
  exact finiteNativeDualFullSourceChartMap_gradedOverlap_value
    𝒜 𝓑 a b ha hb hinja hinjab ell y
end LinearStudy
