module
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
universe u v w x
/-- Preserve the SAME nonempty parameter open and ALL original index
witnesses,while deriving a proved extra law at one chosen index.
The chosen index never changes the original parameter open. -/
theorem parameterFamily_enrich_at_fixedIndex_preserving_allIndices
    {U : Type u} {W : Type v} {I : Type w} {E : W → I → Type x}
    {B1 B2 : U → Prop} {G : U → W → Prop}
    {P R : ∀ (w : W) (i : I),E w i → Prop}
    (family : ∃ a : U,B1 a ∧ B2 a ∧
      ∀ w : W,G a w → ∀ k : I,∃ e : E w k,P w k e ∧ R w k e)
    (k0 : I) {T : ∀ (w : W) (e : E w k0),P w k0 e → Prop}
    (build : ∀ (w : W) (e : E w k0) (he : P w k0 e),T w e he) :
    ∃ a : U,B1 a ∧ B2 a ∧ ∀ w : W,G a w →
      (∀ k : I,∃ e : E w k,P w k e ∧ R w k e) ∧
      (∃ e : E w k0,∃ he : P w k0 e,R w k0 e ∧ T w e he) := by
  obtain ⟨a,h1,h2,hall⟩ := family
  refine ⟨a,h1,h2,fun w hw => ?_⟩
  obtain ⟨e,he,hR⟩ := hall w hw k0
  exact ⟨hall w hw,e,he,hR,build w e he⟩
end LinearStudy
