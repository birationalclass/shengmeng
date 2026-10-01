module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.JacobsonSpace

@[expose] public section
namespace Negativity
open AlgebraicGeometry
universe u

/-- In an actual Jacobson scheme, a closed component not contained in a
closed support has a closed point outside that support. No point-existence
input is assumed. -/
theorem exists_closedPoint_outside_support (X : Scheme) [JacobsonSpace X]
    (F Z : Set X) (hF : IsClosed F) (hZ : IsClosed Z) (hnot : ¬ F ⊆ Z) :
    ∃ x : X, x ∈ F ∧ x ∉ Z ∧ IsClosed ({x} : Set X) := by
  have hn : (F \ Z).Nonempty := by
    obtain ⟨x, hx, hnx⟩ := Set.not_subset.mp hnot
    exact ⟨x, hx, hnx⟩
  have hlc : IsLocallyClosed (F \ Z) := by
    exact hF.isLocallyClosed.inter hZ.isOpen_compl.isLocallyClosed
  obtain ⟨x, hx, hc⟩ := nonempty_inter_closedPoints hn hlc
  exact ⟨x, hx.1, hx.2, hc⟩

/-- For schemes locally of finite type over an actual field, Jacobsonness is
derived from mathlib, so it need not be an additional point-selection input. -/
theorem finiteType_exists_closedPoint_outside_support (k : Type u) [Field k]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (F Z : Set X) (hF : IsClosed F) (hZ : IsClosed Z) (hnot : ¬ F ⊆ Z) :
    ∃ x : X, x ∈ F ∧ x ∉ Z ∧ IsClosed ({x} : Set X) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  exact exists_closedPoint_outside_support X F Z hF hZ hnot

end Negativity
