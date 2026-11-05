module
public import Mathlib.Algebra.Category.Grp.Basic
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open CategoryTheory
universe u
/-- Pointwise form of a proved scalar square on fixed original groups. -/
theorem originalAdditiveScalarSquare_apply
    {X Y : AddCommGrpCat.{u}} {a : X ⟶ X} {j : X ⟶ Y} {d : Y ⟶ Y}
    (w : a ≫ j = j ≫ d) (x : X) : j (a x) = d (j x) :=
  ConcreteCategory.congr_hom w x
end LinearStudy
