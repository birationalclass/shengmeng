module
public import Linear.NativeOriginalGlobalAffineHomSourceAction
public import Linear.NativeNormalizationPushforwardGlobalHomSourceValues
public import Linear.SchemePushforwardOriginalSourceAction
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

/-- The SAME actual native pushforward chart map factors through
the SAME original base/source zero-chart comparison and source section map. -/
theorem nativeNormalizationPushforwardChartSectionMap_original_source_value
    (a : R) (ha : a ∈ 𝒜 1)
    (ell : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a) :
    let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
    letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
    let 𝒟 := coextensionGradedPiece 𝒜 𝓑
    let hD := coextensionProjectiveGradeCompatibility 𝒜 𝓑
    let M := nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0
    nativeNormalizationPushforwardChartSectionMap 𝒜 𝓑 𝒟
      (hR := coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑)
      (hS := hD) a ha ell =
      (show Γ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj M,
        Proj.basicOpen 𝒜 a) from
        nativeProjectiveZeroChartSectionMap 𝓑 𝒟 hD (algebraMap R S a)
          ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha)
          (nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha ell)) := rfl

theorem nativeNormalizationPushforwardChartSectionMap_original_source_inverse_value
    (a : R) (ha : a ∈ 𝒜 1)
    (d : nativeGradedModuleAwayZero 𝓑 (coextensionGradedPiece 𝒜 𝓑) (algebraMap R S a)) :
    let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
    letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
    let 𝒟 := coextensionGradedPiece 𝒜 𝓑
    let hD := coextensionProjectiveGradeCompatibility 𝒜 𝓑
    let M := nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0
    nativeNormalizationPushforwardChartSectionMap 𝒜 𝓑 𝒟
      (hR := coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑)
      (hS := hD) a ha ((nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm d) =
      (show Γ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj M,
        Proj.basicOpen 𝒜 a) from
        nativeProjectiveZeroChartSectionMap 𝓑 𝒟 hD (algebraMap R S a)
          ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha) d) := by
  dsimp only
  rw [nativeNormalizationPushforwardChartSectionMap_original_source_value,
    Equiv.apply_symm_apply]
end LinearStudy
