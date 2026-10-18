module
public import Linear.ParameterFamilyEnrichPreserveShared
public import Linear.ProjectivePulledOriginalAugmentationZero
public import Linear.ParameterPolynomialFamilyIntersection
public import Linear.ProjectivePulledOriginalSetupGlobalGeometricZeroFamily
public import Linear.ProjectivePulledOriginalSetupChartCokernelLambdaZeroFamily
public import Linear.ProjectivePulledKoszulOriginalAmbientCover
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
attribute [local irreducible] projectivePulledOriginalGlobalGeometricZeroStatement
  projectivePulledOriginalCokernelLambdaStatement projectivePulledOriginalWholeTopCokernelStatement
  projectivePulledOriginalChartDataCutStatement projectivePulledOriginalChartDataCutZeroStatement
variable {n p : ℕ}
/-- SAME original common NONEMPTY parameter open BEFORE ALL integer k.
Retain SAME e/he,old global/local class-zero laws,whole Hom cokernel,
actual original augmentation formula,lambda and cover. Add that ALL
actual top-functional classes are killed by precomposition with the
SAME zero augmentation. Canonical duality and original theorems stay OPEN. -/
def projectivePulledOriginalSetupAugmentationKernelFamilyProof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (hrn : p+1 < n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (L : Fin ((p+1)+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :=
  parameterFamily_enrich_preserving_shared
    (T := fun w k e he => projectivePulledOriginalAugmentationZeroStatement f V L hL w k e he)
    (projectivePulledOriginalSetupGlobalGeometricZeroFamilyProof
      f V hrn hq hf hV L hL hinj hfinite x0 hx0)
    (fun w k e he _ => projectivePulledOriginalAugmentationZeroStatement_proof
      (by omega) f V L hL w k e he)
end LinearStudy
