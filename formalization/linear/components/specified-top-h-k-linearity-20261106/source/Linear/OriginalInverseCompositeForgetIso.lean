module
public import Mathlib.CategoryTheory.EqToHom
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open CategoryTheory
universe u v u' v'

/-- Recover the original inverse comparison and its second factor
after identifying the target of the forgotten forward comparison. -/
theorem originalInverseCompositeForgetIso
    {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
    (F : C ⥤ A) {X U D : C} {Y : A}
    (I : X ≅ U) (J : F.obj X ≅ Y) (B : X ≅ D)
    (e : F.obj U = Y) (h : F.map I.hom ≫ eqToHom e = J.hom) :
    eqToIso e.symm ≪≫ F.mapIso (I.symm ≪≫ B) = J.symm ≪≫ F.mapIso B := by
  have hj : F.mapIso I ≪≫ eqToIso e = J := Iso.ext h
  rw [← hj]
  subst Y
  simp [Functor.mapIso_trans, Functor.mapIso_symm]

end LinearStudy
#check LinearStudy.originalInverseCompositeForgetIso
#print axioms LinearStudy.originalInverseCompositeForgetIso
