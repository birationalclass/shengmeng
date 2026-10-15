module
@[expose] public section
set_option autoImplicit false
namespace LinearStudy
universe u v w

/-- Retain the DERIVED cover witness when the actual constructed map
mentions that witness. The SAME parameter open is chosen BEFORE all
indices. This adds a proved cover to the conclusion,not an assumption. -/
theorem parameterFamily_of_dependent_cover {U : Type u} {W : Type v} {I : Type w}
    (B1 B2 : U → Prop) (G : U → W → Prop) (C : W → Prop)
    (P : ∀ w : W,C w → I → Prop)
    (cover : ∃ u : U,B1 u ∧ B2 u ∧ ∀ w : W,G u w → C w)
    (build : ∀ (w : W) (hc : C w) (i : I),P w hc i) :
    ∃ u : U,B1 u ∧ B2 u ∧ ∀ w : W,G u w → ∃ hc : C w,∀ i : I,P w hc i :=
  Exists.elim cover (fun u h =>
    ⟨u,h.1,h.2.1,fun w hw => ⟨h.2.2 w hw,fun i => build w (h.2.2 w hw) i⟩⟩)

end LinearStudy
