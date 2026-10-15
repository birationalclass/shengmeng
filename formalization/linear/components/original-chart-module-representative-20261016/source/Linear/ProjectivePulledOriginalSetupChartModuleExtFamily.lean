module
public import Linear.ProjectivePulledOriginalChartModuleExt
public import Linear.ProjectivePulledOriginalSetupResolution
public import Linear.ParameterFamilyEnrichWitness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
attribute [local irreducible] projectivePulledOriginalChartModuleExtLaw
variable {n r : ℕ}

/-- Original Setup derives ONE NONEMPTY parameter open BEFORE ALL integer
k,retaining the SAME whole-cut quotient augmentation/quasiiso and actual
original X0 MODULE representative comparison. Derive positive module
exactness from that actual augmentation;coefficient isos remain explicit
at the general boundary. No independent conventional-frame formula,
internal sheaf Ext/support or completed original4.2 is asserted. -/
def projectivePulledOriginalSetupChartModuleExtFamilyProof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (hrn : r < n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :=
  parameterFamily_enrich_exists_proof
    (T := fun w k e he => projectivePulledOriginalChartModuleExtLaw f V L hL w k e)
    (projectivePulledLinearSectionOriginalSetupResolutionProof
      f V hrn hq hf hV L hL hinj hfinite x0 hx0)
    (fun w k e he => projectivePulledOriginalChartModuleExtLaw_proof f V L hL w k e)

end LinearStudy
