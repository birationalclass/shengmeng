module
public import Linear.CategoricalScalarSquareComposition
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open CategoryTheory
universe u v
/-- Substitute a proved equality of the original public comparison in a
proved scalar square,without changing either original scalar action. -/
theorem originalEndomorphismSquare_of_comparison_eq
    {C : Type u} [Category.{v} C] {X Y : C}
    {a : X ⟶ X} {d : Y ⟶ Y} {j j0 : X ⟶ Y}
    (hj : j = j0) (w : a ≫ j0 = j0 ≫ d) : a ≫ j = j ≫ d := by
  rw [hj]
  exact w
end LinearStudy
#check LinearStudy.originalEndomorphismSquare_of_comparison_eq
#print axioms LinearStudy.originalEndomorphismSquare_of_comparison_eq
