module
public import Linear.NativeNormalizationDualGlobalHomChartMorphism
import all Linear.NativeNormalizationDualGlobalHomChartMorphism
public import Linear.SchemeModuleHomAffineChartSections
public import Linear.AffineQuasicoherentSourceMorphisms
public import Linear.SchemeModuleSpecChartSectionsLinear
public import Linear.NativeNormalizationPushforwardGlobalHomChartLinear
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
namespace LinearStudy
attribute [local irreducible] nativeNormalizationProjectiveMap schemeModuleHomModuleSheaf
  nativeNormalizationPushforwardGlobalHomChartLinearEquiv
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

/-- An ACTUAL local section of Hom(F,H) on the ORIGINAL base chart,
constructed from the SAME whole-chart comparison morphism. This is the
local object to glue, rather than a family of unchecked point functions. -/
def nativeNormalizationDualChartHomSection
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (hs : Function.Bijective
      (nativeProjectiveChartDegreeZeroSectionMap 𝓑 (coextensionGradedPiece 𝒜 𝓑)
        (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 1 (algebraMap R S a)
          ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha)))
    (hq : (nativeProjectiveModuleSheaf 𝓑 (coextensionGradedPiece 𝒜 𝓑)
      (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 0).IsQuasicoherent) :=
  let M := nativeProjectiveModuleSheaf 𝓑 (coextensionGradedPiece 𝒜 𝓑)
    (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 0
  let F := (Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj M
  let P := (Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
    (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)
  let Q : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
  let H := schemeModuleHomModuleSheaf P Q
  (schemeModuleHomAffineChartSectionsEquiv F H (Proj.basicOpen 𝒜 a)
    (CommRingCat.of (HomogeneousLocalization.Away 𝒜 a))
      (Proj.basicOpenIsoSpec 𝒜 a ha (by decide))).symm
    (nativeNormalizationDualGlobalHomChartMorphism 𝒜 𝓑 a ha hinj hs hq)
end LinearStudy
