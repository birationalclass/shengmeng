module
public import Mathlib.CategoryTheory.Iso
@[expose] public section
set_option maxHeartbeats 5000
namespace LinearStudy
open CategoryTheory
universe u v
/-- Underlying morphism equality from a proved original isomorphism factorization. -/
theorem originalIsoTransHom_of_eq {C : Type u} [Category.{v} C] {X Y Z : C}
    {old : X ≅ Z} {e : X ≅ Y} {j : Y ≅ Z} (h : old = e ≪≫ j) :
    old.hom = e.hom ≫ j.hom := by
  simpa only [Iso.trans_hom] using congrArg (fun t => t.hom) h
end LinearStudy
#check LinearStudy.originalIsoTransHom_of_eq
#print axioms LinearStudy.originalIsoTransHom_of_eq
