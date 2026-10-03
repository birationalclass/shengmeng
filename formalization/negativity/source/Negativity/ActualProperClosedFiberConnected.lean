module
public import Negativity.FiberCharacteristicLifting
public import Negativity.ActualClosedFibersConnectedFromAffineCharacteristicLifts
public import Negativity.ActualProperCechKernelVanishing

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: actual closed fibers of a proper birational morphism
to a normal integral locally Noetherian scheme are connected. The actual
cohomology bound, finite-thickening characteristic extension and global
function lift are constructed, with no formal-functions premise. -/
theorem actual_proper_birational_closed_fibers_connected
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) :
    ∀ y : Y, IsClosed ({y} : Set Y) → ConnectedSpace (f.fiber y) := by
  apply actual_closed_fibers_connected_of_affine_characteristic_lifts f hf hnY
  intro U v hv S hS
  letI : IsAffine U.1 := U.2
  obtain ⟨ι, hι, V, hcover, c, hc⟩ := actual_proper_affine_cech_kernel_vanishing
    (f ∣_ U.1) (actualClosedPointIdeal U.1 v)
  letI : Fintype ι := hι
  exact actual_closed_fiber_characteristic_lifts_of_cech_kernel_vanishing
    (f ∣_ U.1) v hv V (le_of_eq hcover.symm) c hc S hS

#print axioms actual_proper_birational_closed_fibers_connected
end
end Negativity
