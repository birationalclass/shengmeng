module
public import Linear.ProjectivePulledOriginalChartAugmentationLaw
public import Linear.ProjectivePulledOriginalSetupResolution
public import Linear.ParameterFamilyEnrichWitness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
attribute [local irreducible] projectivePulledOriginalChartAugmentationLaw
variable {n r : ℕ}

/-- Original Setup derives ONE NONEMPTY parameter open BEFORE ALL integer
k,with the SAME actual whole-cut quotient augmentation/quasiiso,its
zero-component formula and ACTUAL whole-chain X0 chart augmentation
square. The original source equality and target transport are proved,
not new premises. SAME top-frame and joint Ext representative comparison
remain separate obligations. -/
def projectivePulledOriginalSetupChartAugmentationFamilyProof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (hrn : r < n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :=
  parameterFamily_enrich_exists_proof
    (T := fun w k e he => projectivePulledOriginalChartAugmentationLaw f V L hL w k e)
    (projectivePulledLinearSectionOriginalSetupResolutionProof
      f V hrn hq hf hV L hL hinj hfinite x0 hx0)
    (fun w k e he => projectivePulledOriginalChartAugmentationLaw_proof f V L hL w k e)

end LinearStudy