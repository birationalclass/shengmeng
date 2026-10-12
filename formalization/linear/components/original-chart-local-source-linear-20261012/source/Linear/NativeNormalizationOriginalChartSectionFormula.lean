module
public import Linear.NativeNormalizationDualGlobalHomChartMorphism
public import Linear.NativeNormalizationDualChartMorphismSections
public import Linear.NativePushforwardGlobalHomAllSourceFunctions
public import Linear.NativeNormalizationPushforwardStructureChart
public import Linear.ActualAffineAlgebraDualInternalHomLinear
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
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
attribute [local irreducible] schemeModuleHomModuleSheaf nativeProjectiveModuleSheaf
  nativeNormalizationProjectiveMap nativeProjectiveChartDegreeZeroSectionMap
  nativeNormalizationDualGlobalHomChartMorphism
  nativeNormalizationPushforwardGlobalHomChartLinearEquiv

/-- The SAME original native chart morphism has its already proved
section formula under the ORIGINAL ADDITIVE chart transports. No
agreement hypothesis is assumed and no new chart morphism is selected. -/
theorem nativeNormalizationDualGlobalHomChartMorphism_additive_sections
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (hs : Function.Bijective
      (nativeProjectiveChartDegreeZeroSectionMap 𝓑 (coextensionGradedPiece 𝒜 𝓑)
        (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 1 (algebraMap R S a)
          ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha)))
    (hq : (nativeProjectiveModuleSheaf 𝓑 (coextensionGradedPiece 𝒜 𝓑)
      (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 0).IsQuasicoherent) :
    let M := nativeProjectiveModuleSheaf 𝓑 (coextensionGradedPiece 𝒜 𝓑)
      (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 0
    let f := nativeNormalizationProjectiveMap 𝒜 𝓑
    let F := (Scheme.Modules.pushforward f).obj M
    let P := (Scheme.Modules.pushforward f).obj (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)
    let N : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
    let H := schemeModuleHomModuleSheaf P N
    let j := Proj.awayι 𝒜 a ha (by decide)
    let U := Proj.basicOpen 𝒜 a
    let hi : j ''ᵁ ⊤ = U := j.image_top_eq_opensRange.trans
      (Proj.opensRange_awayι 𝒜 a ha (by decide))
    let C := nativeNormalizationDualGlobalHomChartMorphism 𝒜 𝓑 a ha hinj hs hq
    let Φ := nativeNormalizationPushforwardGlobalHomChartLinearEquiv 𝒜 𝓑 a ha hinj hs
    ∀ t : Γ(F,U),
    C.app ⊤ (schemeModuleSpecChartSectionsEquiv F j U hi t) =
      schemeModuleSpecChartSectionsEquiv H j U hi (Φ t) := by
  dsimp only
  intro t
  exact nativeNormalizationDualGlobalHomChartMorphism_sections 𝒜 𝓑 a ha hinj hs hq t
end LinearStudy
