module
public import Linear.ProjectivePulledOriginalWholeTopCokernelStatement
public import Linear.ProjectivePulledOriginalSetupResolution
public import Linear.ParameterFamilyEnrichWitness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
attribute [local irreducible] projectivePulledOriginalWholeTopCokernelStatement
variable {n r : ℕ}

/-- Original Setup DERIVES ONE NONEMPTY parameter open BEFORE ALL integer
 twists,with SAME original quotient augmentation and ACTUAL native iterated
 WHOLE highest Hom-cokernel representative equal to SAME original top functional for EVERY original
 positive rank. Local a|S and original Lemmas4.1/4.2 remain open. -/
def projectivePulledOriginalSetupWholeTopCokernelFamilyProof
    (hr : 0 < r)
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (hrn : r < n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :=
  parameterFamily_enrich_exists_proof
    (T := fun w k e he => projectivePulledOriginalWholeTopCokernelStatement f V L hL w k e he)
    (projectivePulledLinearSectionOriginalSetupResolutionProof
      f V hrn hq hf hV L hL hinj hfinite x0 hx0)
    (fun w k e he => projectivePulledOriginalWholeTopCokernelStatement_proof hr f V L hL w k e he)

end LinearStudy