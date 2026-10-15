module
@[expose] public section
set_option autoImplicit false
namespace LinearStudy
universe u v w x

/-- Retain the actual derived augmentation witness while adding a proved
law depending on its quasiiso proof. The SAME nonempty parameter open
is chosen BEFORE all indices; no conclusion is replaced by an input. -/
theorem parameterFamily_enrich_exists_proof
    {U : Type u} {W : Type v} {I : Type w} {E : W → I → Type x}
    {B1 B2 : U → Prop} {G : U → W → Prop}
    {P R : ∀ (w : W) (i : I), E w i → Prop}
    {T : ∀ (w : W) (i : I) (e : E w i), P w i e → Prop}
    (family : ∃ u : U,B1 u ∧ B2 u ∧
      ∀ w : W,G u w → ∀ i : I,∃ e : E w i,P w i e ∧ R w i e)
    (build : ∀ (w : W) (i : I) (e : E w i) (he : P w i e),T w i e he) :
    ∃ u : U,B1 u ∧ B2 u ∧ ∀ w : W,G u w → ∀ i : I,
      ∃ e : E w i,∃ he : P w i e,R w i e ∧ T w i e he := by
  obtain ⟨u,h1,h2,hall⟩ := family
  refine ⟨u,h1,h2,?_⟩
  intro w hw i
  obtain ⟨e,he,hR⟩ := hall w hw i
  exact ⟨e,he,hR,build w i e he⟩

end LinearStudy
