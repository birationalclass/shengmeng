module
public import Linear.TopOpenFreeAbelianSheafSectionsNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
/-- The SAME actual free-open sheaf/section equivalence is additive. -/
def topOpenFreeAbelianSheafHomSectionsAddEquiv (X : TopCat.{u}) (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ((topOpenFreeAbelianSheafFunctor X).obj U ⟶ F) ≃+ F.obj.obj (op U) where
  toEquiv := topOpenFreeAbelianSheafHomEquiv X U F
  map_add' a b := by
    simp only [topOpenFreeAbelianSheafHomEquiv, Equiv.trans_apply]
    rfl
end LinearStudy
