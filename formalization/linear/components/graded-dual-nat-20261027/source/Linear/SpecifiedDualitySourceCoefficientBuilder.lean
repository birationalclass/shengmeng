module
public import Linear.SpecifiedDualityCoefficientTransfer
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open CategoryTheory
universe u v
/-- Compose the two ORIGINAL coefficient squares,with source and target
factorizations supplied independently. Every square remains an explicit
remaining input here and is proved in concrete applications. -/
theorem originalSpecifiedDualityCoefficientSquare_of_sourceFactorizations
    {C : Type u} [Category.{v} C] {A H D : C}
    (e : A ≅ H) (j : A ≅ D) (old : H ≅ D) (hold : old=e.symm ≪≫ j)
    (A' H' D' : C) (e' : A' ≅ H') (j' : A' ≅ D') (old' : H' ≅ D')
    (hold' : old'=e'.symm ≪≫ j') (a : A ⟶ A') (h : H ⟶ H') (d : D ⟶ D')
    (h1 : a ≫ e'.hom=e.hom ≫ h) (h2 : a ≫ j'.hom=j.hom ≫ d) :
    h ≫ old'.hom=old.hom ≫ d :=
  originalComparisonIsoCoefficientSquare_of_factorizations e.symm e'.symm j j'
    old old' hold hold' h a d
    (show CommSq a e.hom e'.hom h from ⟨h1⟩).vert_inv.w h2
end LinearStudy
