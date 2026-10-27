module
public import Mathlib.CategoryTheory.Iso
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open CategoryTheory
universe u v
/-- Substitute a proved exact equality of the final morphism in a proved
factorization. All categorical objects remain fixed. -/
theorem originalMorphismFactorization_eq_of_eq
    {C : Type u} [Category.{v} C] {A B D : C}
    {old : A ⟶ D} {e : A ⟶ B} {j k : B ⟶ D}
    (h : old = e ≫ j) (hj : j = k) : old = e ≫ k := by
  rw [h,hj]
end LinearStudy
