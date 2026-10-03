module
public import Negativity.ActualSchemeConnectedOfCharacteristic
public import Negativity.FiberIdempotentConstancy
import Mathlib.Tactic
@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- If every actual clopen characteristic function on an actual fiber lifts to a global
source regular function, a proper birational morphism to a normal integral Noetherian base
has that actual fiber connected. Nonemptiness is proved from proper birational surjectivity;
no lift is assumed to be idempotent. -/
theorem actual_proper_birational_fiber_connected_of_clopen_characteristic_lifts
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) (y : Y)
    (hlift : ∀ (S : Set (f.fiber y)) (hS : IsClopen S),
      ∃ s : Γ(X,⊤), (f.fiberι y).appTop s = actualClopenCharacteristic (f.fiber y) S hS) :
    ConnectedSpace (f.fiber y) := by
  obtain ⟨x, hx⟩ := (proper_birational_surjective f hf).surj y
  have hxrange : x ∈ Set.range (f.fiberι y) := by
    rw [f.range_fiberι y]
    exact hx
  obtain ⟨z, _⟩ := hxrange
  let : Nonempty (f.fiber y) := ⟨z⟩
  have : Nonempty (⊤ : (f.fiber y).Opens) := ⟨⟨z, trivial⟩⟩
  have : Nontrivial Γ(f.fiber y,⊤) := (f.fiber y).component_nontrivial ⊤
  apply actual_scheme_connected_of_characteristic_sections_trivial
  intro S hS
  obtain ⟨s, hs⟩ := hlift S hS
  obtain ⟨c, hc⟩ := actual_proper_birational_fiber_lift_is_constant f hf hnY y s
  have hce : actualFiberConstantMap f y c = actualClopenCharacteristic (f.fiber y) S hS :=
    hc.trans hs
  have hcinj : Function.Injective (actualFiberConstantMap f y) :=
    RingHom.injective (actualFiberConstantMap f y)
  have hcid : c * c = c := by
    apply hcinj
    rw [map_mul, hce, actual_clopen_characteristic_idempotent]
  rcases localRing_idempotent_trivial (Y.residueField y) c hcid with h0 | h1
  · left
    rw [← hce, h0, map_zero]
  · right
    rw [← hce, h1, map_one]

#print axioms actual_proper_birational_fiber_connected_of_clopen_characteristic_lifts
end
end Negativity
