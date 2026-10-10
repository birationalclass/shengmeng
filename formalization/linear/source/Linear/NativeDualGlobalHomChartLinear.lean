module
public import Linear.NativeNormalizationGlobalAffineHomLinear
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000
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
/-- Original finite dual chart elements correspond LINEARLY to actual global Hom chart sections.
This uses the ORIGINAL affine dual and ORIGINAL global-to-affine Hom equivalence. -/
def nativeDualGlobalHomChartLinearEquiv
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a))) :
    let M := (Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
      (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)
    let N : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
    letI := nativeNormalizationGlobalHomChartModule 𝒜 𝓑 a ha
    nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a
      ≃ₗ[HomogeneousLocalization.Away 𝒜 a]
        Γ(schemeModuleHomModuleSheaf M N,Proj.basicOpen 𝒜 a) := by
  dsimp only
  exact (nativeAffineInternalHomSectionsLinearEquiv 𝒜 𝓑 a ha hinj).trans
    (nativeNormalizationGlobalAffineHomSectionsLinearEquiv 𝒜 𝓑 a ha).symm
end LinearStudy
