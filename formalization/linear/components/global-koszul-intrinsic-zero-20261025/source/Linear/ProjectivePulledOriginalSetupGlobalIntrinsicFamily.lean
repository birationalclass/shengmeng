module
public import Linear.ProjectivePulledOriginalChartDataCutStatement
public import Linear.ProjectivePulledOriginalChartDataCutZero
public import Linear.ProjectivePulledOriginalSetupWholeTopCokernelLambdaFamily
public import Linear.ParameterFamilyEnrichWitness
public import Linear.ParameterFamilyProjectSharedWitness
public import Linear.ProjectivePulledOriginalGlobalIntrinsicZero
public import Linear.ProjectivePulledOriginalSetupIntrinsicZeroFamily
public import Linear.ProjectivePulledKoszulOriginalAmbientCover
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] projectivePulledOriginalChartDataCutStatement
  projectivePulledOriginalChartDataCutZeroStatement projectivePulledOriginalChartIntrinsicMapZeroStatement
  projectivePulledOriginalWholeTopCokernelStatement projectivePulledOriginalCokernelLambdaStatement
attribute [local irreducible] projectivePulledOriginalGlobalIntrinsicZeroStatement
attribute [local irreducible] projectivePulledLinearKoszulComplex projectivePulledWholeCutResolutionTarget
  homogeneousQuotientGrading
variable {n p : ℕ}
/-- ORIGINAL geometry derives GLOBAL vanishing of the SAME original
Ext class iff the ORIGINAL coefficient map has zero ACTUAL cut pullback.
ONE nonempty parameter open precedes ALL integer twists;actual augmentation,
quasiiso,source vanishings,lambda and support are DERIVED. Nonzero local
trace weights,canonical identification and original4.1/4.2/main OPEN. -/
theorem projectivePulledOriginalSetupGlobalIntrinsicZeroFamilyProof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (hrn : p+1 < n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (L : Fin ((p+1)+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ c : MvPolynomial (Fin ((p+1)+1)) ℂ, c ≠ 0 ∧
      (∃ w : Fin ((p+1)+1) → ℂ, MvPolynomial.eval w c ≠ 0) ∧
      ∀ w : Fin ((p+1)+1) → ℂ, MvPolynomial.eval w c ≠ 0 →
        letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
        ∀ k : ℤ,
          ∃ e : cokernel ((projectivePulledLinearKoszulComplex f V L hL w k).d 1 0) ≅
              projectivePulledWholeCutResolutionTarget f V L hL w k,
          ∃ he : QuasiIso (originalChainCokernelTargetAugmentation
              (projectivePulledLinearKoszulComplex f V L hL w k)
              (projectivePulledWholeCutResolutionTarget f V L hL w k) e),
            (originalChainCokernelTargetAugmentation
              (projectivePulledLinearKoszulComplex f V L hL w k)
              (projectivePulledWholeCutResolutionTarget f V L hL w k) e).f 0 =
                cokernel.π ((projectivePulledLinearKoszulComplex f V L hL w k).d 1 0) ≫ e.hom ∧
            projectivePulledOriginalGlobalIntrinsicZeroStatement f V L hL w k e he := by
  exact parameterFamily_project_from_sharedFacts
    (T := fun w k e he => projectivePulledOriginalGlobalIntrinsicZeroStatement f V L hL w k e he)
    (parameterPolynomialFamily_intersection
      (projectivePulledOriginalSetupIntrinsicZeroFamilyProof f V hrn hq hf hV L hL hinj hfinite x0 hx0)
      (projectivePulledLinearSection_exists_original_ambient_cover f V hq hf hV L hL hinj hfinite x0 hx0))
    (fun w hLambda hCover k e he _ =>
      projectivePulledOriginalGlobalIntrinsicZeroStatement_proof f V L hL w k e he hCover (hLambda k))
end LinearStudy
