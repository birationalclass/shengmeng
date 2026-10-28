module
public import Linear.ConcreteOriginalScalarSquareApply
@[expose] public section
set_option maxHeartbeats 5000
namespace LinearStudy
open CategoryTheory
universe u
/-- The concrete-category extensionality criterion for an original scalar square. -/
theorem originalAdditiveScalarSquare_of_apply
    {X Y : AddCommGrpCat} {a : X ⟶ X} {j : X ⟶ Y} {d : Y ⟶ Y}
    (w : ∀ x : X,j (a x) = d (j x)) : a ≫ j = j ≫ d :=
  ConcreteCategory.ext_apply w
/-- Pointwise scalar naturality after independent equalities of the original maps. -/
theorem originalScalarSquare_apply_of_calibrations
    {A B : Type u} {a : A → A} {j j0 : A → B} {d d0 : B → B}
    (hj : ∀ x,j x = j0 x) (hd : ∀ y,d y = d0 y)
    (w : ∀ x,j0 (a x) = d0 (j0 x)) (x : A) : j (a x) = d (j x) :=
  (hj (a x)).trans ((w x).trans ((hd (j0 x)).symm.trans (congrArg d (hj x).symm)))
end LinearStudy
#check LinearStudy.originalAdditiveScalarSquare_of_apply
#print axioms LinearStudy.originalAdditiveScalarSquare_of_apply
