module
public import Linear.ProjectivePulledOriginalCutActualSectionSequence
public import Linear.ProjectivePulledOriginalSetupResolution
public import Linear.ParameterFamilyEnrichFixedIndex
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] projectivePulledOriginalCutActualSectionSequenceStatement
variable {n r : ℕ}
/-- Derive the SAME complete Setup augmentation family and its actual
section law at the fixed original t. Infer the exact dependent result
from the existing family combinator,so the kernel does not repeatedly
normalize a handwritten duplicate of the giant quotient/sheaf type.
This is a genuine Prop-valued PROOF TERM,not a statement definition.
Its uniform caller below supplies hSeq from PROVED original-V Serre. -/
def projectivePulledOriginalSetupCutActualSectionFamilyProof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (hrn : r < n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet)
    (hSeq : ∀ (w : Fin (r+1) → ℂ)
      (e : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
        cokernel ((projectivePulledLinearKoszulComplex f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)).d 1 0) ≅
          projectivePulledWholeCutResolutionTarget f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1))
      (he : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
        QuasiIso (originalChainCokernelTargetAugmentation
          (projectivePulledLinearKoszulComplex f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1))
          (projectivePulledWholeCutResolutionTarget f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)) e)),
      projectivePulledOriginalCutActualSectionSequenceStatement f V L hL w e he) :=
  parameterFamily_enrich_at_fixedIndex_preserving_allIndices
    (T := fun w e he => projectivePulledOriginalCutActualSectionSequenceStatement f V L hL w e he)
    (projectivePulledLinearSectionOriginalSetupResolutionProof
      f V hrn hq hf hV L hL hinj hfinite x0 hx0)
    ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)
    (fun w e he => hSeq w e he)
end LinearStudy
