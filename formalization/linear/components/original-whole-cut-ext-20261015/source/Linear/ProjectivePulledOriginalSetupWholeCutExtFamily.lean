module
public import Linear.ProjectivePulledOriginalChainWholeCutExtNaturality
public import Linear.ProjectivePulledOriginalSetupResolution
public import Linear.ParameterFamilyEnrichWitness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
variable {n r : ℕ}

/-- Original Setup: derive ONE NONEMPTY parameter open BEFORE ALL integer
k, its actual whole-cut quotient augmentation and quasiiso, together with
the actual derived-roof Ext class coefficient-pushforward formula.
The original r<n discharges the previous dimension/nonzero-ideal inputs.
No desired Ext-class, source exactness or comparison certificate is a
new hypothesis. Internal SHEAF Ext/connecting maps/proper duality and
original Lemmas4.1/4.2 remain unproved. -/
def projectivePulledOriginalSetupWholeCutExtFamilyProof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (hrn : r < n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :=
  parameterFamily_enrich_exists_proof
    (projectivePulledLinearSectionOriginalSetupResolutionProof
      f V hrn hq hf hV L hL hinj hfinite x0 hx0)
    (fun w k e he => projectivePulledOriginalChainWholeCutExtAllPushProof f V L hL w k e he)

end LinearStudy
