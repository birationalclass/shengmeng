module
public import Negativity.ClosedFiberThickeningIso
public import Negativity.RelativeInfinitesimalIdempotents
public import Negativity.AffineBaseCechVanishing
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

def actualClosedFiberToPower {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) (hy : IsClosed ({y} : Set Y)) (n : ℕ) :
    f.fiber y ⟶ actualRelativePowerThickening f (actualClosedPointIdeal Y y) n :=
  actualClosedFiberIdealMap f y hy ≫ IdealSheafData.inclusion (by
    simpa only [pow_one] using
      actual_relative_power_ideal_antitone f (actualClosedPointIdeal Y y)
        (show 1 ≤ n + 1 by omega))

@[reassoc (attr := simp)]
theorem actual_closed_fiber_to_power_fac {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) (hy : IsClosed ({y} : Set Y)) (n : ℕ) :
    actualClosedFiberToPower f y hy n ≫
        (((actualClosedPointIdeal Y y) ^ (n + 1)).comap f).subschemeι = f.fiberι y := by
  simp [actualClosedFiberToPower]

theorem actual_closed_fiber_to_power_point {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) (hy : IsClosed ({y} : Set Y)) (n : ℕ) (x : f.fiber y) :
    actualRelativePowerHomeomorph f (actualClosedPointIdeal Y y) n
      (actualClosedFiberToPower f y hy n x) = actualClosedFiberIdealMap f y hy x := by
  apply Subtype.ext
  change (((actualClosedPointIdeal Y y) ^ (n + 1)).comap f).subschemeι
      (actualClosedFiberToPower f y hy n x) =
    ((actualClosedPointIdeal Y y).comap f).subschemeι (actualClosedFiberIdealMap f y hy x)
  have h1 := congrArg (fun g : f.fiber y ⟶ X => g x)
    (actual_closed_fiber_to_power_fac f y hy n)
  have h2 := congrArg (fun g : f.fiber y ⟶ X => g x)
    (actual_closed_fiber_ideal_map_fac f y hy)
  exact h1.trans h2.symm

/-- Final theorem: a clopen characteristic function on the actual closed
fiber extends to every actual finite thickening. No infinite formal section,
cohomology bound or idempotent lift is supplied. -/
theorem actual_closed_fiber_characteristic_extends_to_thickening
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (hy : IsClosed ({y} : Set Y))
    (S : Set (f.fiber y)) (hS : IsClopen S) (n : ℕ) :
    ∃ b : Γ(actualRelativePowerThickening f (actualClosedPointIdeal Y y) n, ⊤),
      (actualClosedFiberToPower f y hy n).appTop b =
        actualClopenCharacteristic (f.fiber y) S hS := by
  let e := asIso (actualClosedFiberIdealMap f y hy)
  let T := e.inv ⁻¹' S
  have hT : IsClopen T := hS.preimage e.inv.continuous
  let V := (actualRelativePowerHomeomorph f (actualClosedPointIdeal Y y) n) ⁻¹' T
  have hV : IsClopen V := hT.preimage
    (actualRelativePowerHomeomorph f (actualClosedPointIdeal Y y) n).continuous
  refine ⟨actualClopenCharacteristic _ V hV, ?_⟩
  rw [actual_clopen_characteristic_pullback]
  have hset : (actualClosedFiberToPower f y hy n) ⁻¹' V = S := by
    ext x
    change e.inv (actualRelativePowerHomeomorph f (actualClosedPointIdeal Y y) n
      (actualClosedFiberToPower f y hy n x)) ∈ S ↔ x ∈ S
    rw [actual_closed_fiber_to_power_point]
    have hx : e.inv (e.hom x) = x := by
      change (e.hom ≫ e.inv) x = x
      rw [e.hom_inv_id]
      rfl
    rw [show actualClosedFiberIdealMap f y hy = e.hom from rfl, hx]
  simp only [hset]

end
end Negativity
