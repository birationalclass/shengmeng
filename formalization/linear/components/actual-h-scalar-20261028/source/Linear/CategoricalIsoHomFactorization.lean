module
public import Mathlib.CategoryTheory.Iso
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open CategoryTheory
universe u v
/-- Calibrate the underlying morphism of a specified factorization using
an independently proved exact equality for its source comparison. -/
theorem originalIsoHomFactorization_of_eq
    {C : Type u} [Category.{v} C] {A B D : C}
    (old : A ≅ D) (e : A ≅ B) (j : B ≅ D) (k : B ⟶ D)
    (h : old = e ≪≫ j) (hj : j.hom = k) : old.hom = e.hom ≫ k := by
  rw [h,Iso.trans_hom,hj]
/-- Substitute a proved literal morphism equality in a checked scalar square. -/
theorem originalMorphismScalarSquare_of_eq
    {C : Type u} [Category.{v} C] {A D : C}
    (old j : A ⟶ D) (h : old = j) (a : A ⟶ A) (d : D ⟶ D)
    (w : a ≫ j = j ≫ d) : a ≫ old = old ≫ d := by
  rw [h]
  exact w
end LinearStudy
