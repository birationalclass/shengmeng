module
public import Linear.ProjectivePulledOriginalChartDataCutStatement
public import Linear.ProjectivePulledOriginalChartDataCutZero
public import Linear.ProjectivePulledOriginalSetupWholeTopCokernelLambdaFamily
public import Linear.ParameterFamilyEnrichWitness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
attribute [local irreducible] projectivePulledOriginalChartDataCutStatement
  projectivePulledOriginalChartDataCutZeroStatement
  projectivePulledOriginalWholeTopCokernelStatement projectivePulledOriginalCokernelLambdaStatement
variable {n p : ℕ}
/-- One original NONEMPTY parameter open before ALL integer twists,with
SAME derived e/he,exact original degree-zero augmentation,the original
WHOLE highest-Hom-cokernel class,the actual original X0-chart class
formula AND actual geometric-pullback zero criterion for ALL
quasicoherent coefficients and functionals,and the SAME
canonical lambda bijection for all coefficients and positive degrees.
No chart/class/lambda/augmentation certificate is a geometric premise.
Independent conventional-frame compatibility,global support/gluing,theta4.1,uniformm
and original4.1/4.2/main remain outside this combined proved family. -/
def projectivePulledOriginalSetupChartCokernelLambdaZeroFamilyProof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (hrn : p+1 < n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (L : Fin ((p+1)+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :=
  parameterPolynomialFamily_intersection
    (parameterFamily_enrich_exists_proof
      (T := fun w k e he => projectivePulledOriginalWholeTopCokernelStatement f V L hL w k e he ∧
        projectivePulledOriginalChartDataCutStatement f V L hL w k e he ∧
        projectivePulledOriginalChartDataCutZeroStatement f V L hL w k e he)
      (projectivePulledLinearSectionOriginalSetupResolutionProof
        f V hrn hq hf hV L hL hinj hfinite x0 hx0)
      (fun w k e he =>
        ⟨projectivePulledOriginalWholeTopCokernelStatement_proof (by omega) f V L hL w k e he,
          projectivePulledOriginalChartDataCutStatement_proof f V L hL w k e he,
          projectivePulledOriginalChartDataCutZeroStatement_proof f V L hL w k e he⟩))
    (projectivePulledLinearSection_exists_originalCokernelCanonicalLambda_bijective
      f V hq hf hV L hL hinj hfinite x0 hx0)
end LinearStudy
