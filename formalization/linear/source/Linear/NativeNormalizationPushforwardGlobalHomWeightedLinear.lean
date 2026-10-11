module
public import Linear.NativeNormalizationPushforwardWeightedSections
public import Linear.NativeDualGlobalHomWeightedOverlapLinear
public import Linear.NativeCoextensionBaseSourceCharts
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
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
def nativeNormalizationPushforwardGlobalHomWeightedOverlapLinearEquiv [IsDomain R]
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1) (hab : a*b ≠ 0)
    (hinja : Function.Injective (algebraMap R (Localization.Away a)))
    (hinj : Function.Injective (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)))
    (hs : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap 𝓑
      (coextensionGradedPiece 𝒜 𝓑) (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 2
      (algebraMap R S (a*b))
      ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem (SetLike.mul_mem_graded ha hb)))) :
    let 𝒟 := coextensionGradedPiece 𝒜 𝓑
    let M := nativeProjectiveModuleSheaf 𝓑 𝒟 (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 0
    let P := (Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
      (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)
    let N : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
    letI := nativeNormalizationPushforwardChartModule 𝒜 𝓑 (a*b) M
    letI := nativeNormalizationGlobalWeightedHomChartModule 𝒜 𝓑 2 (by decide) (a*b) (SetLike.mul_mem_graded ha hb)
    Γ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj M,
      Proj.basicOpen 𝒜 (a*b)) ≃ₗ[HomogeneousLocalization.Away 𝒜 (a*b)]
        Γ(schemeModuleHomModuleSheaf P N,Proj.basicOpen 𝒜 (a*b)) := by
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
  dsimp only
  let 𝒟 := coextensionGradedPiece 𝒜 𝓑
  let hR := coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑
  let hS := coextensionProjectiveGradeCompatibility 𝒜 𝓑
  let θ := nativeNormalizationPushforwardWeightedChartSectionMap 𝒜 𝓑 𝒟
    (hR := hR) (hS := hS) 2 (a*b) (SetLike.mul_mem_graded ha hb)
  have hθ := nativeNormalizationPushforwardWeightedChartSectionMap_bijective 𝒜 𝓑 𝒟
    (hR := hR) (hS := hS) 2 (a*b) (SetLike.mul_mem_graded ha hb) hs
  let E := LinearEquiv.ofBijective θ hθ
  exact E.symm.trans (nativeDualGlobalHomWeightedOverlapLinearEquiv 𝒜 𝓑 a b ha hb hab hinja hinj)

end LinearStudy
