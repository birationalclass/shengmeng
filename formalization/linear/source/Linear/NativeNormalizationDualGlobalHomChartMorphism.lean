module
public import Linear.NativeNormalizationPushforwardSourceChartTilde
public import Linear.AffineQuasicoherentSourceMorphisms
public import Linear.SchemeModuleSpecChartSectionsLinear
public import Linear.SchemeModuleSpecChartMorphism
import all Linear.SchemeModuleSpecChartMorphism
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

/-- The SAME original pushforward-dual/Hom chart comparison extends to
an actual module-sheaf morphism on the entire affine chart. Standard
source quasicoherence and chart section bijectivity are explicit inputs;
both have been independently derived for the original integral V.
Global gluing and canonical identification are not asserted. -/
def nativeNormalizationDualGlobalHomChartMorphism
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
    let F := (Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj M
    let P := (Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
      (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)
    let Q : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
    F.restrict (Proj.awayι 𝒜 a ha (by decide)) ⟶
      (schemeModuleHomModuleSheaf P Q).restrict (Proj.awayι 𝒜 a ha (by decide)) := by
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  letI : IsScalarTower K S D := IsScalarTower.of_compHom K S D
  let 𝒟 := coextensionGradedPiece 𝒜 𝓑
  let hD := coextensionProjectiveGradeCompatibility 𝒜 𝓑
  let M := nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0
  letI : M.IsQuasicoherent := hq
  let F := (Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj M
  let P := (Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
    (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)
  let Q : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
  let H := schemeModuleHomModuleSheaf P Q
  let Ai := CommRingCat.of (HomogeneousLocalization.Away 𝒜 a)
  let j := Proj.awayι 𝒜 a ha (by decide)
  let U := Proj.basicOpen 𝒜 a
  have hi : j ''ᵁ ⊤ = U := j.image_top_eq_opensRange.trans
    (Proj.opensRange_awayι 𝒜 a ha (by decide))
  let e := nativeNormalizationPushforwardSourceChartTildeIso 𝒜 𝓑 𝒟 hD a ha hs
  letI : (F.restrict j).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Ai).ringCatSheaf).prop_of_iso e inferInstance
  letI := nativeNormalizationPushforwardChartModule 𝒜 𝓑 a M
  letI := nativeNormalizationGlobalHomChartModule 𝒜 𝓑 a ha
  let C := nativeNormalizationPushforwardGlobalHomChartLinearEquiv 𝒜 𝓑 a ha hinj hs
  exact schemeModuleSpecChartMorphism F H j U hi
    (Proj.awayToSection 𝒜 a) (originalProjectiveChartScalar_appLE 𝒜 a ha) C

end LinearStudy
