module
public import Linear.TopOpenFreeAbelianSheaf
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
/-- Original open sections represent morphisms from its free abelian sheaf. -/
def topOpenFreeAbelianSheafHomEquiv (X : TopCat.{u}) (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ((topOpenFreeAbelianSheafFunctor X).obj U ⟶ F) ≃ F.obj.obj (op U) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).homEquiv _ F).trans
    (((AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ).homEquiv _ F.obj).trans
      uliftYonedaEquiv)

end LinearStudy
