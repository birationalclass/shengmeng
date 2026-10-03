module
public import Negativity.ActualProperClosedFiberConnected
public import Negativity.ConnectedSchemeGlobalIdempotents

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: every actual closed-fiber idempotent of a proper
birational morphism to a normal integral locally Noetherian base comes
from an actual global source section, hence from the pushforward stalk.
Actual closed-fiber connectedness is proved internally. -/
theorem actual_proper_birational_closed_fiber_idempotent_descends
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (y : Y) (hy : IsClosed ({y} : Set Y))
    (e : Γ(f.fiber y, ⊤)) (he : e * e = e) :
    ∃ s : Γ(X, ⊤), (f.fiberι y).appTop s = e := by
  letI : ConnectedSpace (f.fiber y) :=
    actual_proper_birational_closed_fibers_connected f hf hnY y hy
  exact actual_connected_fiber_idempotent_lifts_from_global f y e he

#print axioms actual_proper_birational_closed_fiber_idempotent_descends
end
end Negativity
