module
public import Linear.SchemeModulePresentationDataGlobalProjection
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/-- Existence of a comparison preserving the ACTUAL quotient projection.
The unit condition is explicit here;original applications derive it. -/
theorem schemeModuleMappedPresentationDataGlobalProjection_exists
    {X Y : Scheme} (j : X ⟶ Y) [IsOpenImmersion j]
    [(Scheme.Modules.restrictFunctor j).Additive]
    [(Scheme.Modules.restrictFunctor j).PreservesHomology]
    (d : mappedChainPresentationData (Scheme.Modules.restrictFunctor j))
    (hu : IsIso ((Scheme.Modules.restrictAdjunction j).unit.app (cokernel (d.1.d 1 0)))) :
    ∃ E : cokernel (d.1.d 1 0) ≅ (Scheme.Modules.pushforward j).obj d.2.2.2.1.pt,
      schemeModuleMappedPresentationDataGlobalProjection j d E :=
  ⟨schemeModuleMappedPresentationDataGlobalIso j d hu,
    schemeModuleMappedPresentationDataGlobalIso_projection j d hu⟩

/-- Preserve the SAME parameter-open witness BEFORE ALL indices when
passing from a proved cover to the actual family of projection proofs. -/
theorem parameterFamily_of_cover {U W I : Type*}
    (B1 B2 : U → Prop) (G : U → W → Prop) (C : W → Prop) (P : W → I → Prop)
    (cover : ∃ u : U,B1 u ∧ B2 u ∧ ∀ w : W,G u w → C w)
    (build : ∀ w : W,C w → ∀ i : I,P w i) :
    ∃ u : U,B1 u ∧ B2 u ∧ ∀ w : W,G u w → ∀ i : I,P w i := by
  obtain ⟨u,h1,h2,hc⟩ := cover
  exact ⟨u,h1,h2,fun w hw i => build w (hc w hw) i⟩

end LinearStudy
