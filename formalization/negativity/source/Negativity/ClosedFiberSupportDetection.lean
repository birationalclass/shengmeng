module

public import Negativity.ConstructibleClosedPoint
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
universe u
noncomputable section

/-- Final theorem: for an actual finite-type morphism of Noetherian
schemes with Jacobson target, an actual closed subset is all-or-nothing
on every fiber as soon as this holds on all closed-point fibers.
Chevalley's theorem constructs the mixed-fiber locus, and genuine
constructible closed-point detection supplies a closed witness if it
is nonempty. Nonclosed fibers require no extra connectedness premise. -/
theorem actual_fiber_closed_subset_dichotomy_of_closed_points
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [JacobsonSpace Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (S : Set X) (hS : IsClosed S)
    (hc : ∀ y : Y, IsClosed ({y} : Set Y) →
      (∀ x : X, f x = y → x ∉ S) ∨ (∀ x : X, f x = y → x ∈ S)) :
    ∀ y : Y, (∀ x : X, f x = y → x ∉ S) ∨
      (∀ x : X, f x = y → x ∈ S) := by
  classical
  have hco : IsConstructible Sᶜ :=
    (NoetherianSpace.isCompact Sᶜ).isConstructible hS.isOpen_compl
  have hcs : IsConstructible S := by simpa using hco.compl
  have hbad : IsConstructible (f '' S ∩ f '' Sᶜ) :=
    (f.isConstructible_image hcs).inter (f.isConstructible_image hco)
  intro y
  by_contra hn
  have hnone := (not_or.mp hn).1
  have hnall := (not_or.mp hn).2
  obtain ⟨x, hx, hxS⟩ : ∃ x : X, f x = y ∧ x ∈ S := by
    simpa only [not_forall, not_imp, not_not, exists_prop] using hnone
  obtain ⟨w, hw, hwS⟩ : ∃ w : X, f w = y ∧ w ∉ S := by
    simpa only [not_forall, not_imp, exists_prop] using hnall
  have hne : (f '' S ∩ f '' Sᶜ).Nonempty :=
    ⟨y, ⟨x, hxS, hx⟩, ⟨w, hwS, hw⟩⟩
  obtain ⟨z, hz, hzc⟩ := noetherian_constructible_contains_closed_point _ hbad hne
  obtain ⟨a, haS, haz⟩ := hz.1
  obtain ⟨b, hbS, hbz⟩ := hz.2
  rcases hc z hzc with h | h
  · exact h a haz haS
  · exact hbS (h b hbz)

end
end Negativity
