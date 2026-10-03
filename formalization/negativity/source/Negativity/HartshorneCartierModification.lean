module

public import Negativity.NormalHartshorneModification
public import Negativity.ProjectiveProductCartierSections
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: an actual proper integral variety over an affine
base has an actual normal integral proper birational surjective
modification carrying a constructed actual Cartier affine-section
cover. Hartshorne's cover, graph, finite product projection, finite
normalization and all effective section geometry are constructed.
No projectivity, modification, divisor or section witness is an input. -/
theorem exists_actual_hartshorne_cartier_modification
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsAffine Y]
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType b]
    (f : X ⟶ Y) [IsProper f] :
    ∃ (N : Scheme.{u}) (π : N ⟶ X),
      IsIntegral N ∧ IsLocallyNoetherian N ∧
      (∀ z : N, IsIntegrallyClosed (N.presheaf.stalk z)) ∧
      IsProper π ∧ BirationalMorphism π ∧ Surjective π ∧
      ∃ (_ : IsIntegral N) (A : CartierAtlas N N),
        Nonempty (CartierAffineSectionCover A N) := by
  obtain ⟨n, d, P, N, p, a, π, q, hp, ha, haff, hint, hnoeth, hnormal,
    hπ, hbir, hsur, hq, hw⟩ := exists_actual_normal_hartshorne_modification k b f
  have : IsIntegral N := hint
  have : IsFinite q := hq
  obtain ⟨A, hS⟩ := exists_actual_projective_product_cartier_sections Γ(Y, ⊤) n d q a haff
  exact ⟨N, π, hint, hnoeth, hnormal, hπ, hbir, hsur, hint, A, hS⟩

end
end Negativity
