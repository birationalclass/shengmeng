module
public import Linear.NativeOriginalGlobalAffineHomSourceAction
public import Linear.NativeGlobalHomSourceChartModule
public import Linear.NativeGlobalHomSourceChartScalar
public import Linear.ActualAffineHomSourceScalar
public import Linear.ActualAffineNativeDualSourceLinear
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] normalizationHomogeneousSourceChartAlgebra

/-- Scalar compatibility for the SAME original degree-one global Hom
chart, using the source module structures already constructed on each side. -/
theorem nativeNormalizationGlobalAffineHomSections_source_smul
    (a : R) (ha : a ∈ 𝒜 1)
    (b : HomogeneousLocalization.Away 𝓑 (algebraMap R S a))
    (h : Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
        (SheafOfModules.unit (Proj 𝓑).ringCatSheaf))
      (SheafOfModules.unit (Proj 𝒜).ringCatSheaf), Proj.basicOpen 𝒜 a)) :
    let A := HomogeneousLocalization.Away 𝒜 a
    let B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
    letI := nativeNormalizationGlobalHomSourceChartModule 𝒜 𝓑 a
    letI := actualAffineOriginalHomSourceModule (A := A) (B := B)
    nativeNormalizationGlobalAffineHomSectionsLinearEquiv 𝒜 𝓑 a ha (b • h) =
      b • nativeNormalizationGlobalAffineHomSectionsLinearEquiv 𝒜 𝓑 a ha h := by
  dsimp only
  rw [nativeNormalizationGlobalHomSourceChartModule_smul,
    actualAffineOriginalHomSourceModule_smul]
  have hs := nativeNormalizationGlobalAffineHomSections_original_source_action 𝒜 𝓑 a ha b h
  dsimp only at hs
  have hb := eq_of_heq (actualAffineAlgebraStructurePushforwardIso_element_value
    (A := HomogeneousLocalization.Away 𝒜 a) b)
  rw [hb] at hs
  exact hs
end LinearStudy
