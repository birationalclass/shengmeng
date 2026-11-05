module
public import Mathlib.CategoryTheory.CommSq
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open CategoryTheory
universe u v
/-- Composition of two proved coefficient squares on fixed objects. -/
theorem originalEndomorphismSquare_comp
    {C : Type u} [Category.{v} C] {A B D : C}
    {a : A ⟶ A} {e : A ⟶ B} {b : B ⟶ B} {j : B ⟶ D} {d : D ⟶ D}
    (w1 : a ≫ e = e ≫ b) (w2 : b ≫ j = j ≫ d) :
    a ≫ (e ≫ j) = (e ≫ j) ≫ d :=
  ((show CommSq a e e b from ⟨w1⟩).vert_comp
    (show CommSq b j j d from ⟨w2⟩)).w
end LinearStudy
