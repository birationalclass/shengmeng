module
public import Linear.SpecifiedDualitySourceCoefficientBuilder
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open CategoryTheory
universe u v
/-- Cache three ORIGINAL comparisons together with their proved exact factorization.
This is data,not a theorem and not a new comparison choice. -/
def originalSpecifiedDualityFactorizationData
    {C : Type u} [Category.{v} C] {A H D : C}
    (e : A ≅ H) (j : A ≅ D) (old : H ≅ D) (hold : old=e.symm ≪≫ j) :
    {p : (A ≅ H) × (A ≅ D) × (H ≅ D) // p.2.2=p.1.symm ≪≫ p.2.1} :=
  ⟨(e,j,old),hold⟩
/-- TWO original squares give naturality of the SAME cached specified maps. -/
theorem originalSpecifiedDualityFactorizationData_coefficient
    {C : Type u} [Category.{v} C] {A H D A' H' D' : C}
    (p : {z : (A ≅ H) × (A ≅ D) × (H ≅ D) // z.2.2=z.1.symm ≪≫ z.2.1})
    (p' : {z : (A' ≅ H') × (A' ≅ D') × (H' ≅ D') // z.2.2=z.1.symm ≪≫ z.2.1})
    (a : A ⟶ A') (h : H ⟶ H') (d : D ⟶ D')
    (h1 : a ≫ p'.val.1.hom=p.val.1.hom ≫ h)
    (h2 : a ≫ p'.val.2.1.hom=p.val.2.1.hom ≫ d) :
    h ≫ p'.val.2.2.hom=p.val.2.2.hom ≫ d :=
  originalSpecifiedDualityCoefficientSquare_of_sourceFactorizations p.val.1 p.val.2.1 p.val.2.2 p.prop
    A' H' D' p'.val.1 p'.val.2.1 p'.val.2.2 p'.prop a h d h1 h2
end LinearStudy
