module

public import Negativity.ClosedFiberInfinitesimalIdempotent
public import Negativity.LocalConnectedness
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem, explicitly conditional: the actual closed fiber is
connected if the constructed relative completion comparison is bijective.
The actual fiber, ideal, limit, local completion and idempotent contradiction
are established internally. Bijectivity is the remaining geometric input
and is written in the statement; no proper connectedness theorem is claimed. -/
theorem actual_closed_fiber_connected_of_relative_formal_functions
    {X Y : Scheme.{u}} [IsAffine Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Surjective f] (y : Y) (hy : IsClosed ({y} : Set Y))
    (hff : Function.Bijective
      (actualRelativeFormalFunctionsMap f (actualClosedPointIdeal Y y))) :
    ConnectedSpace (f.fiber y) := by
  classical
  let I := actualClosedPointIdeal Y y
  let R := AdicCompletion (I.ideal ⟨⊤, isAffineOpen_top Y⟩) Γ(Y, ⊤)
  let p : R →+* actualRelativeInfinitesimalSections f I :=
    actualRelativeFormalFunctionsMap f I
  have : IsLocalRing R := actual_closed_point_completion_local Y y hy
  have : Nonempty (f.fiber y) := by
    obtain ⟨x, hx⟩ := f.surjective y
    exact ⟨(f.fiberHomeo y).symm ⟨x, by simpa using hx⟩⟩
  apply connectedSpace_iff_clopen.mpr
  refine ⟨inferInstance, ?_⟩
  intro S hS
  by_contra hn
  have hn := not_or.mp hn
  obtain ⟨a, ha, h0, h1⟩ :=
    actual_closed_fiber_infinitesimal_nontrivial_idempotent f y hy S hS hn.1 hn.2
  obtain ⟨r, hr⟩ := hff.2 a
  have hid : r * r = r := by
    apply hff.1
    change p (r * r) = p r
    rw [map_mul, hr, ha]
  rcases localRing_idempotent_trivial R r hid with hzero | hone
  · apply h0
    rw [← hr, hzero]
    exact map_zero p
  · apply h1
    rw [← hr, hone]
    exact map_one p

end
end Negativity
