module
public import Linear.NativeNormalizationPushforwardGlobalHomChartLinear
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra
/-- The actual local pushforward/Hom comparison retains the ORIGINAL
native finite-dual section map, and therefore its original pairing values. -/
theorem nativeNormalizationPushforwardGlobalHomChartLinearEquiv_apply_source_section
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (hs : Function.Bijective
      (nativeProjectiveChartDegreeZeroSectionMap 𝓑 (coextensionGradedPiece 𝒜 𝓑)
        (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 1 (algebraMap R S a)
          ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha)))
    (ell : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a) :
    let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
    letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
    let 𝒟 := coextensionGradedPiece 𝒜 𝓑
    let M := nativeProjectiveModuleSheaf 𝓑 𝒟 (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 0
    letI := nativeNormalizationPushforwardChartModule 𝒜 𝓑 a M
    letI := nativeNormalizationGlobalHomChartModule 𝒜 𝓑 a ha
    nativeNormalizationPushforwardGlobalHomChartLinearEquiv 𝒜 𝓑 a ha hinj hs
      (nativeNormalizationPushforwardChartSectionMap 𝒜 𝓑 𝒟
        (hR := coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑)
        (hS := coextensionProjectiveGradeCompatibility 𝒜 𝓑) a ha ell) =
      nativeDualGlobalHomChartLinearEquiv 𝒜 𝓑 a ha hinj ell := by
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
  dsimp only
  let theta := nativeNormalizationPushforwardChartSectionMap 𝒜 𝓑
    (coextensionGradedPiece 𝒜 𝓑)
    (hR := coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑)
    (hS := coextensionProjectiveGradeCompatibility 𝒜 𝓑) a ha
  have hb := nativeBaseSourceChartSectionMap_bijective 𝒜 𝓑 (coextensionGradedPiece 𝒜 𝓑)
    (coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑)
    (coextensionProjectiveGradeCompatibility 𝒜 𝓑) a ha hs
  let E := LinearEquiv.ofBijective theta hb
  change nativeDualGlobalHomChartLinearEquiv 𝒜 𝓑 a ha hinj (E.symm (E ell)) = _
  rw [LinearEquiv.symm_apply_apply]
end LinearStudy
