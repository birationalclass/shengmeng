module
public import Negativity.ClopenCharacteristicSection
import Mathlib.Tactic
@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- An actual nonempty scheme is connected when the actual characteristic functions
of its clopen subsets are trivial. This uses their actual stalk germs. -/
theorem actual_scheme_connected_of_characteristic_sections_trivial
    (X : Scheme.{u}) [Nonempty X]
    (h : ∀ (S : Set X) (hS : IsClopen S),
      actualClopenCharacteristic X S hS = 0 ∨ actualClopenCharacteristic X S hS = 1) :
    ConnectedSpace X := by
  classical
  apply connectedSpace_iff_clopen.mpr
  refine ⟨inferInstance, ?_⟩
  intro S hS
  rcases h S hS with hzero | hone
  · left
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hg := actual_clopen_characteristic_germ X S hS x
    rw [hzero, map_zero, ite_eq_left hx] at hg
    exact zero_ne_one hg
  · right
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    have hg := actual_clopen_characteristic_germ X S hS x
    rw [hone, map_one, ite_eq_right hx] at hg
    exact one_ne_zero hg

#print axioms actual_scheme_connected_of_characteristic_sections_trivial
end
end Negativity
