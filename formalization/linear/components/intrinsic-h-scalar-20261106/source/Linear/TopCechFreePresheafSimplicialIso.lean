module
public import Linear.TopCechFreeSheafResolution
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
open CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
namespace LinearStudy
/-- The ACTUAL free abelian presheaf Cech simplicial object before sheafification. -/
def topCechFreeAbelianPresheafAugmented (X : TopCat.{u}) {ι : Type u} (U : ι → Opens X) :
    SimplicialObject.Augmented ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (((SimplicialObject.Augmented.whiskering _ _).obj
    ((Functor.whiskeringRight (Opens X)ᵒᵖ (Type u) AddCommGrpCat.{u}).obj
      AddCommGrpCat.free)).obj (FormalCoproduct.mk _ U).shrinkYonedaCech)

set_option backward.defeqAttrib.useBackward true in
/-- Compare to the native evaluation of the ORIGINAL free-open PRESHEAF functor.
All coproducts are formed in presheaves;no sheaf-coproduct search is needed. -/
def topCechFreePresheafSimplicialIso (X : TopCat.{u}) {ι : Type u} (U : ι → Opens X) :
    (topCechFreeAbelianPresheafAugmented X U).left ≅
      (FormalCoproduct.mk _ U).cech ⋙
        (FormalCoproduct.eval.{u} (Opens X) ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})).obj
          (topOpenFreeAbelianPresheafFunctor X) := by
  let W := (Functor.whiskeringRight (Opens X)ᵒᵖ (Type u) AddCommGrpCat.{u}).obj
    AddCommGrpCat.free
  let E := FormalCoproduct.eval.{u} (Opens X) ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
  let e : shrinkYoneda.{u} ⋙ W ≅ topOpenFreeAbelianPresheafFunctor X :=
    Functor.isoWhiskerRight (uliftYonedaIsoShrinkYoneda.{u,u,u}.symm) W
  change (((FormalCoproduct.mk _ U).cech ⋙
      (FormalCoproduct.eval.{u} (Opens X) ((Opens X)ᵒᵖ ⥤ Type u)).obj shrinkYoneda.{u}) ⋙ W) ≅ _
  refine (Functor.associator _ _ _) ≪≫ ?_
  let a : ((FormalCoproduct.eval.{u} (Opens X) ((Opens X)ᵒᵖ ⥤ Type u)).obj
      shrinkYoneda.{u}) ⋙ W ≅ E.obj (shrinkYoneda.{u} ⋙ W) :=
    (FormalCoproduct.evalObjCompIso.{u} shrinkYoneda.{u} W).symm
  let b : E.obj (shrinkYoneda.{u} ⋙ W) ≅ E.obj (topOpenFreeAbelianPresheafFunctor X) :=
    E.mapIso e
  exact Functor.isoWhiskerLeft (FormalCoproduct.mk _ U).cech (a ≪≫ b)
end LinearStudy
