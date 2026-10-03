module

public import Negativity.RelativeInfinitesimalIdempotents
public import Negativity.ClosedPointFiberThickenings
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: a nontrivial clopen decomposition of the actual
scheme-theoretic fiber over an actual closed base point produces a
nontrivial idempotent in the actual relative infinitesimal function limit.
The base-point ideal, fiber comparison and compatible functions are all
constructed. The source may be nonaffine; no comparison input is required. -/
theorem actual_closed_fiber_infinitesimal_nontrivial_idempotent
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (hy : IsClosed ({y} : Set Y))
    (S : Set (f.fiber y)) (hS : IsClopen S) (h0 : S ≠ ∅) (h1 : S ≠ Set.univ) :
    ∃ a : actualRelativeInfinitesimalSections f (actualClosedPointIdeal Y y),
      a * a = a ∧ a ≠ 0 ∧ a ≠ 1 := by
  classical
  let e := actualClosedPointFiberHomeomorph f y hy
  let T := e ⁻¹' S
  have hT : IsClopen T := hS.preimage e.continuous
  have hT0 : T ≠ ∅ := by
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr h0
    apply Set.nonempty_iff_ne_empty.mp
    exact ⟨e.symm x, by simpa [T] using hx⟩
  have hT1 : T ≠ Set.univ := by
    intro ht
    apply h1
    apply Set.eq_univ_of_forall
    intro x
    have hx : e.symm x ∈ T := ht ▸ Set.mem_univ _
    simpa [T] using hx
  exact actual_relative_infinitesimal_nontrivial_idempotent f
    (actualClosedPointIdeal Y y) T hT hT0 hT1

end
end Negativity
