module
public import Negativity.FiberCharacteristicThickening
public import Negativity.RelativeCechSourceLifting
public import Negativity.SchemeSectionLiftRestriction
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

@[reassoc (attr := simp)]
theorem actual_closed_fiber_to_power_transition {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) (hy : IsClosed ({y} : Set Y)) {m n : ℕ} (h : m ≤ n) :
    actualClosedFiberToPower f y hy m ≫
      actualRelativePowerInclusion f (actualClosedPointIdeal Y y) h =
        actualClosedFiberToPower f y hy n := by
  rw [← cancel_mono (((actualClosedPointIdeal Y y) ^ (n + 1)).comap f).subschemeι]
  simp [actualRelativePowerInclusion]

/-- Final theorem: an actual cohomology transition bound yields an actual
global lift of each closed-fiber clopen characteristic. Only one finite
thickening is used; no formal-limit comparison is required. The cohomology
bound remains an explicit premise of this intermediate theorem. -/
theorem actual_closed_fiber_characteristic_lifts_of_cech_kernel_vanishing
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (hy : IsClosed ({y} : Set Y))
    {ι : Type v} (U : ι → X.affineOpens)
    (hU : (⊤ : X.Opens) ≤ iSup (fun k => (U k).1)) (c : ℕ)
    (hvanish : ActualRelativeCechKernelVanishing f (actualClosedPointIdeal Y y) U c)
    (S : Set (f.fiber y)) (hS : IsClopen S) :
    ∃ s : Γ(X, ⊤), (f.fiberι y).appTop s =
      actualClopenCharacteristic (f.fiber y) S hS := by
  let I := actualClosedPointIdeal Y y
  let j := actualRelativePowerInclusion f I (Nat.le_add_right 0 c)
  let i := ((I ^ (0 + c + 1)).comap f).subschemeι
  obtain ⟨b, hb⟩ := actual_closed_fiber_characteristic_extends_to_thickening f y hy S hS (0 + c)
  obtain ⟨s, hs⟩ := actual_relative_source_section_lifting_of_cech_kernel_vanishing
    f I U hU c hvanish 0 b
  refine ⟨s, ?_⟩
  have hj : actualClosedFiberToPower f y hy 0 ≫ j =
      actualClosedFiberToPower f y hy (0 + c) := actual_closed_fiber_to_power_transition f y hy _
  have hi : actualClosedFiberToPower f y hy 0 ≫ j ≫ i = f.fiberι y := by
    rw [← Category.assoc, hj]
    exact actual_closed_fiber_to_power_fac f y hy (0 + c)
  have ht := actual_scheme_section_lift_restriction j i
    (actualClosedFiberToPower f y hy 0) s b hs
  have hleft := congrArg (fun g : f.fiber y ⟶ X => g.appTop s) hi
  have hright := congrArg
    (fun g : f.fiber y ⟶ actualRelativePowerThickening f I (0 + c) => g.appTop b) hj
  exact hleft.symm.trans (ht.trans (hright.trans hb))

#print axioms actual_closed_fiber_characteristic_lifts_of_cech_kernel_vanishing

end
end Negativity
