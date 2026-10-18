module
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
universe u v w x
/-- Enrich the SAME already derived e/he on the SAME parameter open by
two proved shared parameter laws. Keep BOTH laws and the full old result;
no new choices of witnesses or parameter opens are introduced here. -/
theorem parameterFamily_enrich_from_sharedFacts
    {U : Type u} {W : Type v} {I : Type w} {E : W → I → Type x}
    {B1 B2 : U → Prop} {G : U → W → Prop}
    {P : ∀ (w : W) (i : I),E w i → Prop}
    {R T : ∀ (w : W) (i : I) (e : E w i),P w i e → Prop}
    {Q Z : W → Prop}
    (family : ∃ u : U,B1 u ∧ B2 u ∧ ∀ w : W,G u w →
      ((∀ i : I,∃ e : E w i,∃ he : P w i e,R w i e he) ∧ Q w) ∧ Z w)
    (build : ∀ (w : W),Q w → Z w → ∀ (i : I) (e : E w i)
      (he : P w i e),R w i e he → T w i e he) :
    ∃ u : U,B1 u ∧ B2 u ∧ ∀ w : W,G u w →
      (∀ i : I,∃ e : E w i,∃ he : P w i e,R w i e he ∧ T w i e he) ∧ Q w ∧ Z w := by
  obtain ⟨u,h1,h2,hall⟩ := family
  refine ⟨u,h1,h2,?_⟩
  intro w hw
  obtain ⟨⟨hR,hQ⟩,hZ⟩ := hall w hw
  refine ⟨?_,hQ,hZ⟩
  intro i
  obtain ⟨e,he,hr⟩ := hR i
  exact ⟨e,he,hr,build w hQ hZ i e he hr⟩
end LinearStudy
