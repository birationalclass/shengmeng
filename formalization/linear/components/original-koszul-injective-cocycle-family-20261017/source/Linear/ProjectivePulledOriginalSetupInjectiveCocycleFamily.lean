module
public import Linear.ProjectivePulledOriginalWholeCutInjectiveStatement
public import Linear.ProjectivePulledOriginalSetupResolution
public import Linear.ParameterFamilyEnrichWitness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
attribute [local irreducible] projectivePulledOriginalWholeCutInjectiveStatement
variable {n r : ℕ}

/-- Original Setup DERIVES ONE NONEMPTY parameter open BEFORE ALL integer twists,
with SAME actual whole-cut quotient augmentation,quasi-isomorphism,original
ordered top class,and ACTUAL injective cocycle and source cochain homotopy
for EVERY coefficient injective resolution. The a|S and source-iteration
class identities and original Lemmas4.1/4.2 remain separate obligations. -/
def projectivePulledOriginalSetupInjectiveCocycleFamilyProof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (hrn : r < n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :=
  parameterFamily_enrich_exists_proof
    (T := fun w k e he => projectivePulledOriginalWholeCutInjectiveStatement f V L hL w k e he)
    (projectivePulledLinearSectionOriginalSetupResolutionProof
      f V hrn hq hf hV L hL hinj hfinite x0 hx0)
    (fun w k e he => projectivePulledOriginalWholeCutInjectiveStatement_proof f V L hL w k e he)

end LinearStudy