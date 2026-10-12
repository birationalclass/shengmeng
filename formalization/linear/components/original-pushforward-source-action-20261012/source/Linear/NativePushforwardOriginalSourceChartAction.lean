module
public import Linear.NativeOriginalGlobalAffineHomSourceAction
public import Linear.NativeNormalizationPushforwardGlobalHomSourceValues
public import Linear.SchemePushforwardOriginalSourceAction
public import Linear.NativePushforwardOriginalSourceChartValues
public import Linear.NativeAffineSourceChartHomLinear
public import Linear.NativeDualGlobalHomChartLinear
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 150000
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

/-- Actual source multiplication on the original native pushforward
sections agrees with the original source-native chart multiplication. -/
theorem nativeNormalizationPushforwardChartSectionMap_original_source_action
    (a : R) (ha : a ∈ 𝒜 1)
    (b : HomogeneousLocalization.Away 𝓑 (algebraMap R S a))
    (d : nativeGradedModuleAwayZero 𝓑 (coextensionGradedPiece 𝒜 𝓑) (algebraMap R S a)) :
    let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
    letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
    let 𝒟 := coextensionGradedPiece 𝒜 𝓑
    let hD := coextensionProjectiveGradeCompatibility 𝒜 𝓑
    let M := nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0
    let f := nativeNormalizationProjectiveMap 𝒜 𝓑
    let U := Proj.basicOpen 𝒜 a
    let θ := nativeNormalizationPushforwardChartSectionMap 𝒜 𝓑 𝒟
      (hR := coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑) (hS := hD) a ha
    schemePushforwardOriginalSourceActionSection f M U
      (show Γ(Proj 𝓑,f ⁻¹ᵁ U) from (Proj.awayToSection 𝓑 (algebraMap R S a)) b)
      (θ ((nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm d)) =
      θ ((nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm (b • d)) := by
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
  dsimp only
  rw [nativeNormalizationPushforwardChartSectionMap_original_source_inverse_value,
    nativeNormalizationPushforwardChartSectionMap_original_source_inverse_value]
  change (Proj.awayToSection 𝓑 (algebraMap R S a)).hom b •
      (nativeProjectiveZeroChartSectionMap 𝓑 (coextensionGradedPiece 𝒜 𝓑)
        (coextensionProjectiveGradeCompatibility 𝒜 𝓑) (algebraMap R S a)
        ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha) d) = _
  exact (nativeProjectiveZeroChartSectionMap 𝓑 (coextensionGradedPiece 𝒜 𝓑)
    (coextensionProjectiveGradeCompatibility 𝒜 𝓑) (algebraMap R S a)
    ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha)).map_smulₛₗ b d |>.symm
end LinearStudy
