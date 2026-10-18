module
public import Linear.ParameterFamilyEnrichSharedFacts
public import Linear.ParameterPolynomialFamilyIntersection
public import Linear.ProjectivePulledOriginalGlobalGeometricZero
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
/-- ORIGINAL Setup derives ONE NONEMPTY parameter open BEFORE ALL integer
k,with SAME e/he and original degree-zero augmentation formula,whole top
Hom-cokernel class,actual local class formula and local zero criterion.
The original ambient cover DERIVES internal-Ext support and canonical
lambda injectivity is transferred to the SAME whole-cut target. Thus the
SAME actual GLOBAL class vanishes iff its actual ordered coefficient
section has zero genuine pullback on the original nonreduced cut,for ALL
quasicoherent N and functionals. No support,lambda,chart or class law is
a final geometric premise. The original cover and cokernel-lambda laws
are retained. Independently prescribed frame comparison,theta4.1,uniformm
and original4.1/4.2/main remain separate. -/
def projectivePulledOriginalSetupGlobalGeometricZeroFamilyProof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (hrn : p+1 < n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (L : Fin ((p+1)+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :=
  parameterFamily_enrich_from_sharedFacts
    (T := fun w k e he => projectivePulledOriginalGlobalGeometricZeroStatement f V L hL w k e he)
    (parameterPolynomialFamily_intersection
      (projectivePulledOriginalSetupChartCokernelLambdaZeroFamilyProof
        f V hrn hq hf hV L hL hinj hfinite x0 hx0)
      (projectivePulledLinearSection_exists_original_ambient_cover
        f V hq hf hV L hL hinj hfinite x0 hx0))
    (fun w hLambda hCover k e he _ =>
      projectivePulledOriginalGlobalGeometricZeroStatement_proof
        f V L hL w k e he hCover (hLambda k))
end LinearStudy
