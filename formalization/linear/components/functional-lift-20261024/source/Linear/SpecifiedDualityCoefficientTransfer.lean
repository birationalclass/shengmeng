module
public import Linear.CategoricalComparisonCoefficientFactorization
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory
universe u v
/-- Transfer two proved ORIGINAL coefficient squares through the inverse
of the SAME comparison. This is an algebraic transfer,not a proof that
geometric omega/trace has been identified. -/
theorem originalSpecifiedDualityCoefficientSquare_of_comparisonSquares
    {C : Type u} [Category.{v} C] {A A' H H' D D' : C}
    (e : A ≅ H) (e' : A' ≅ H') (j : A ≅ D) (j' : A' ≅ D')
    (a : A ⟶ A') (h : H ⟶ H') (d : D ⟶ D')
    (h1 : a ≫ e'.hom = e.hom ≫ h) (h2 : a ≫ j'.hom = j.hom ≫ d) :
    h ≫ (e'.symm ≪≫ j').hom = (e.symm ≪≫ j).hom ≫ d := by
  let sq : CommSq a e.hom e'.hom h := ⟨h1⟩
  let dsq : CommSq a j.hom j'.hom d := ⟨h2⟩
  exact (sq.vert_inv.vert_comp dsq).w
end LinearStudy
