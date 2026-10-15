module
public import Linear.ProjectivePulledOriginalMappedChainExt
public import Linear.ProjectivePulledOriginalSetupResolution
public import Linear.ParameterFamilyEnrichWitness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
attribute [local irreducible] projectivePulledOriginalMappedChainExtLaw
variable {n r : ℕ}

/-- Original Setup derives ONE NONEMPTY parameter open BEFORE ALL integer
k,with the SAME actual whole-cut quotient augmentation and quasiiso,
its zero-component formula,and native Ext restriction equal to the actual
mapped CHAIN-resolution class. The named equality is an explicit conclusion,not a
premise. Affine MODULE Ext/internal SHEAF Ext/connecting maps stay open. -/
def projectivePulledOriginalSetupMappedChainExtFamilyProof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (hrn : r < n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :=
  parameterFamily_enrich_exists_proof
    (T := fun w k e he => projectivePulledOriginalMappedChainExtLaw f V L hL w k e he)
    (projectivePulledLinearSectionOriginalSetupResolutionProof
      f V hrn hq hf hV L hL hinj hfinite x0 hx0)
    (fun w k e he => projectivePulledOriginalMappedChainExtLaw_proof f V L hL w k e he)

end LinearStudy