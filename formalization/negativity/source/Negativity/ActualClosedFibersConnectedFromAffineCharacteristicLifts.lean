module
public import Negativity.ActualProperBirationalFiberConnectedFromClopenLifts
public import Negativity.FiniteNormalGeometry
public import Negativity.AffineNeighborhoodFiber
import Mathlib.Tactic
@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Characteristic-function lifts on actual affine target neighborhoods give
connected actual closed fibers globally. Normality, birationality, properness,
nonemptiness and the actual fiber comparison are transported by proved geometry. -/
theorem actual_closed_fibers_connected_of_affine_characteristic_lifts
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hlift : ∀ (U : Y.affineOpens) (v : U.1.toScheme), IsClosed ({v} : Set U.1.toScheme) →
      ∀ (S : Set ((f ∣_ U.1).fiber v)) (hS : IsClopen S),
        ∃ s : Γ((f ⁻¹ᵁ U.1).toScheme,⊤),
          ((f ∣_ U.1).fiberι v).appTop s =
            actualClopenCharacteristic ((f ∣_ U.1).fiber v) S hS) :
    ∀ y : Y, IsClosed ({y} : Set Y) → ConnectedSpace (f.fiber y) := by
  intro y hyclosed
  have hycover : y ∈ ⨆ U : Y.affineOpens, U.1 := by
    rw [iSup_affineOpens_eq_top]
    trivial
  obtain ⟨U, hyU⟩ := Opens.mem_iSup.mp hycover
  let v : U.1.toScheme := ⟨y, hyU⟩
  let : Nonempty U.1 := ⟨v⟩
  obtain ⟨x, hx⟩ := (proper_birational_surjective f hf).surj y
  have : Nonempty (f ⁻¹ᵁ U.1) := ⟨x, by change f x ∈ U.1; rw [hx]; exact hyU⟩
  have hv : IsClosed ({v} : Set U.1.toScheme) := by
    have hpreimage : U.1.ι ⁻¹' ({y} : Set Y) = {v} := by
      ext t
      change (t.val = y) ↔ t = v
      constructor
      · intro ht
        exact Subtype.ext ht
      · intro ht
        exact congrArg Subtype.val ht
    rw [← hpreimage]
    exact hyclosed.preimage U.1.ι.continuous
  have hconnected : ConnectedSpace ((f ∣_ U.1).fiber v) :=
    actual_proper_birational_fiber_connected_of_clopen_characteristic_lifts
      (f ∣_ U.1) (birationalMorphism_restrict f hf U.1)
      (normalStalks_restrict Y U.1 hnY) v (hlift U v hv)
  exact (actual_restricted_fiber_connected_iff f U.1 y hyU).mp hconnected

#print axioms actual_closed_fibers_connected_of_affine_characteristic_lifts
end
end Negativity
