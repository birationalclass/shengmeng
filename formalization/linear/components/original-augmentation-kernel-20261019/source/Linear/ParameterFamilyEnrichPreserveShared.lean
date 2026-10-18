module
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
universe u v w x
/-- Preserve the SAME witnesses and ALL previous shared laws while adding
a proved witness-dependent law. No new parameter open or e is chosen. -/
theorem parameterFamily_enrich_preserving_shared
    {U : Type u} {W : Type v} {I : Type w} {E : W → I → Type x}
    {B1 B2 : U → Prop} {G : U → W → Prop}
    {P : ∀ (w : W) (i : I),E w i → Prop}
    {R T : ∀ (w : W) (i : I) (e : E w i),P w i e → Prop}
    {Q : W → Prop}
    (family : ∃ u : U,B1 u ∧ B2 u ∧ ∀ w : W,G u w →
      (∀ i : I,∃ e : E w i,∃ he : P w i e,R w i e he) ∧ Q w)
    (build : ∀ (w : W) (i : I) (e : E w i)
      (he : P w i e),R w i e he → T w i e he) :
    ∃ u : U,B1 u ∧ B2 u ∧ ∀ w : W,G u w →
      (∀ i : I,∃ e : E w i,∃ he : P w i e,R w i e he ∧ T w i e he) ∧ Q w := by
  obtain ⟨u,h1,h2,hall⟩ := family
  refine ⟨u,h1,h2,?_⟩
  intro w hw
  obtain ⟨hR,hQ⟩ := hall w hw
  refine ⟨?_,hQ⟩
  intro i
  obtain ⟨e,he,hr⟩ := hR i
  exact ⟨e,he,hr,build w i e he hr⟩
end LinearStudy
