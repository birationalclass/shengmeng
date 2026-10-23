module
public import Linear.ConcreteAdditiveEquivSquare
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory
universe u
/-- TWO original coefficient objects and their SAME actual additive comparisons.
The original pointwise square gives the original categorical square. -/
theorem additiveEquivIso_coefficient {A B C D : AddCommGrpCat.{u}}
    (e : A ≃+ B) (e' : C ≃+ D) (f : A ⟶ C) (g : B ⟶ D)
    (h : ∀ x,e' (f x) = g (e x)) :
    e.toAddCommGrpIso.hom ≫ g = f ≫ e'.toAddCommGrpIso.hom := by
  ext x
  exact (h x).symm
end LinearStudy
