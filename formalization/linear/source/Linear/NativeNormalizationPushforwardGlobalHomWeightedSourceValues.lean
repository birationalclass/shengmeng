module
public import Linear.NativeNormalizationPushforwardGlobalHomWeightedLinear
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
theorem nativeNormalizationPushforwardGlobalHomWeightedOverlapLinearEquiv_apply_source_section
    [IsDomain R] (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1) (hab : a*b ≠ 0)
    (hinja : Function.Injective (algebraMap R (Localization.Away a)))
    (hinj : Function.Injective (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)))
    (hs : Function.Bijective
      (nativeProjectiveChartDegreeZeroSectionMap 𝓑 (coextensionGradedPiece 𝒜 𝓑)
        (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 2 (algebraMap R S (a*b))
          ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem (SetLike.mul_mem_graded ha hb))))
    (ell : nativeGradedModuleAwayDegreeZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) 2 (a*b)) :
    let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
    letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
    let 𝒟 := coextensionGradedPiece 𝒜 𝓑
    let M := nativeProjectiveModuleSheaf 𝓑 𝒟 (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 0
    letI := nativeNormalizationPushforwardChartModule 𝒜 𝓑 (a*b) M
    letI := nativeNormalizationGlobalWeightedHomChartModule 𝒜 𝓑 2 (by decide) (a*b) (SetLike.mul_mem_graded ha hb)
    nativeNormalizationPushforwardGlobalHomWeightedOverlapLinearEquiv 𝒜 𝓑 a b ha hb hab hinja hinj hs
      (nativeNormalizationPushforwardWeightedChartSectionMap 𝒜 𝓑 𝒟
        (hR := coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑)
        (hS := coextensionProjectiveGradeCompatibility 𝒜 𝓑) 2 (a*b) (SetLike.mul_mem_graded ha hb) ell) =
      nativeDualGlobalHomWeightedOverlapLinearEquiv 𝒜 𝓑 a b ha hb hab hinja hinj ell := by
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
  dsimp only
  let theta := nativeNormalizationPushforwardWeightedChartSectionMap 𝒜 𝓑
    (coextensionGradedPiece 𝒜 𝓑)
    (hR := coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑)
    (hS := coextensionProjectiveGradeCompatibility 𝒜 𝓑) 2 (a*b) (SetLike.mul_mem_graded ha hb)
  have htheta := nativeNormalizationPushforwardWeightedChartSectionMap_bijective 𝒜 𝓑
    (coextensionGradedPiece 𝒜 𝓑)
    (hR := coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑)
    (hS := coextensionProjectiveGradeCompatibility 𝒜 𝓑) 2 (a*b)
    (SetLike.mul_mem_graded ha hb) hs
  let E := LinearEquiv.ofBijective theta htheta
  change nativeDualGlobalHomWeightedOverlapLinearEquiv 𝒜 𝓑 a b ha hb hab hinja hinj (E.symm (E ell)) = _
  rw [LinearEquiv.symm_apply_apply]
end LinearStudy
