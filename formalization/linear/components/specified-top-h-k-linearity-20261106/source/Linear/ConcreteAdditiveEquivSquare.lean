module
public import Mathlib.Algebra.Category.Grp.Basic
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory
universe u
/-- A proved pointwise square for the SAME additive equivalence is the
square of its original categorical isomorphism, with original maps. -/
theorem additiveEquivIso_endomorphism {A B : AddCommGrpCat.{u}}
    (e : A ≃+ B) (f : A ⟶ A) (g : B ⟶ B)
    (h : ∀ x,e (f x) = g (e x)) :
    e.toAddCommGrpIso.hom ≫ g = f ≫ e.toAddCommGrpIso.hom := by
  ext x
  exact (h x).symm
end LinearStudy
