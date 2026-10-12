module
public import Linear.NativeNormalizationPushforwardChartSections
public import Linear.NativeDualGlobalHomChartLinear
public import Linear.NativeCoextensionBaseSourceCharts
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
/-- Exact actual pushforward-to-global-Hom chart comparison.
The only extra input is bijectivity of the actual native source-dual chart section map;
this input is already proved for the original integral projective variety.
This is a local construction and does not assert overlap compatibility or global duality. -/
def nativeNormalizationPushforwardGlobalHomChartLinearEquiv
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (hs : Function.Bijective
      (nativeProjectiveChartDegreeZeroSectionMap 𝓑 (coextensionGradedPiece 𝒜 𝓑)
        (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 1 (algebraMap R S a)
          ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha))) :
    let 𝒟 := coextensionGradedPiece 𝒜 𝓑
    let M := nativeProjectiveModuleSheaf 𝓑 𝒟 (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 0
    let P := (Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
      (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)
    let N : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
    letI := nativeNormalizationPushforwardChartModule 𝒜 𝓑 a M
    letI := nativeNormalizationGlobalHomChartModule 𝒜 𝓑 a ha
    Γ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj M,
      Proj.basicOpen 𝒜 a) ≃ₗ[HomogeneousLocalization.Away 𝒜 a]
        Γ(schemeModuleHomModuleSheaf P N,Proj.basicOpen 𝒜 a) := by
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
  dsimp only
  letI := nativeNormalizationPushforwardChartModule 𝒜 𝓑 a
    (nativeProjectiveModuleSheaf 𝓑 (coextensionGradedPiece 𝒜 𝓑)
      (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 0)
  letI := nativeNormalizationGlobalHomChartModule 𝒜 𝓑 a ha
  have hb := nativeBaseSourceChartSectionMap_bijective 𝒜 𝓑 (coextensionGradedPiece 𝒜 𝓑)
    (coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑)
    (coextensionProjectiveGradeCompatibility 𝒜 𝓑) a ha hs
  let E := LinearEquiv.ofBijective
    (nativeNormalizationPushforwardChartSectionMap 𝒜 𝓑 (coextensionGradedPiece 𝒜 𝓑)
      (hR := coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑)
      (hS := coextensionProjectiveGradeCompatibility 𝒜 𝓑) a ha) hb
  exact E.symm.trans (nativeDualGlobalHomChartLinearEquiv 𝒜 𝓑 a ha hinj)
end LinearStudy
