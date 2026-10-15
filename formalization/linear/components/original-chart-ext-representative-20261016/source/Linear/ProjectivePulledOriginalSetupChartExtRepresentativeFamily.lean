module
public import Linear.ProjectivePulledOriginalChartExtRepresentative
public import Linear.ProjectivePulledOriginalSetupResolution
public import Linear.ParameterFamilyEnrichWitness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
attribute [local irreducible] projectivePulledOriginalChartExtRepresentativeLaw
variable {n r : ℕ}

/-- Original Setup DERIVES ONE NONEMPTY parameter open BEFORE ALL integer
k,with the SAME whole-cut quotient augmentation/quasiiso and actual
original X0 chart Ext representative. The source is the SAME named global
Koszul;the top functional is transported through actual constructed maps.
Its specific module top-frame formula and SHEAF Ext/support remain open. -/
def projectivePulledOriginalSetupChartExtRepresentativeFamilyProof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (hrn : r < n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :=
  parameterFamily_enrich_exists_proof
    (T := fun w k e he => projectivePulledOriginalChartExtRepresentativeLaw f V L hL w k e)
    (projectivePulledLinearSectionOriginalSetupResolutionProof
      f V hrn hq hf hV L hL hinj hfinite x0 hx0)
    (fun w k e he => projectivePulledOriginalChartExtRepresentativeLaw_proof f V L hL w k e)

end LinearStudy
