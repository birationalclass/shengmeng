module
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
universe u v w x
/-- Retain the SAME parameter open,witness e,proof he and first actual
law while replacing the auxiliary conjunction by a proved consequence
of the SAME shared laws. No new choice/open/geometric premise. -/
theorem parameterFamily_project_from_sharedFacts
    {U : Type u} {W : Type v} {I : Type w} {E : W → I → Type x}
    {B1 B2 : U → Prop} {G : U → W → Prop}
    {P : ∀ (w : W) (i : I),E w i → Prop}
    {A B T : ∀ (w : W) (i : I) (e : E w i),P w i e → Prop}
    {Q Z : W → Prop}
    (family : ∃ u : U,B1 u ∧ B2 u ∧ ∀ w : W,G u w →
      ((∀ i : I,∃ e : E w i,∃ he : P w i e,A w i e he ∧ B w i e he) ∧ Q w) ∧ Z w)
    (build : ∀ w,Q w → Z w → ∀ i e he,B w i e he → T w i e he) :
    ∃ u : U,B1 u ∧ B2 u ∧ ∀ w : W,G u w →
      ∀ i : I,∃ e : E w i,∃ he : P w i e,A w i e he ∧ T w i e he := by
  obtain ⟨u,h1,h2,hall⟩ := family
  refine ⟨u,h1,h2,?_⟩
  intro w hw
  obtain ⟨⟨hR,hQ⟩,hZ⟩ := hall w hw
  intro i
  obtain ⟨e,he,ha,hb⟩ := hR i
  exact ⟨e,he,ha,build w hQ hZ i e he hb⟩
end LinearStudy
