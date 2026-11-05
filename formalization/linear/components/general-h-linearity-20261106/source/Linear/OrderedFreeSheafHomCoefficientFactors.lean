module
public import Linear.OrderedFreeSheafHomComplex
public import Linear.FreeOpenHomCoefficientNaturality
public import Linear.FormalCoproductContravariantCoefficientNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
/-- Extract the SAME presheaf-level factor of the already compiled
ordered-free-sheaf Hom/Cech comparison;all original maps are retained. -/
def orderedFreeSheafHomCoefficientPresheafIso (X : Scheme.{u})
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ((orderedFreeOpenFormalPresheafFunctor X) ⋙
      presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).op ⋙
        preadditiveYoneda.obj F ≅
      (FormalCoproduct.evalOp.{u} X.Opens AddCommGrpCat.{u}).obj F.obj := by
  let P := orderedFreeOpenFormalPresheafFunctor X
  let K := topOpenFreeAbelianPresheafFunctor X
  let S := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let YS := preadditiveYoneda.obj F
  let YP := preadditiveYoneda.obj F.obj
  exact Functor.isoWhiskerRight (Functor.opComp P S) YS ≪≫
    Functor.associator P.op S.op YS ≪≫
    Functor.isoWhiskerLeft P.op (nativeAdjunctionHomPresheafIso
      (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}) F) ≪≫
    formalCoproductContravariantEvaluationIso.{u} K YP ≪≫
    (FormalCoproduct.evalOp.{u} X.Opens AddCommGrpCat.{u}).mapIso
      (topOpenFreeAbelianPresheafHomPresheafIso X F)

/-- A SMALL component formula for the SAME previously used five-factor
presheaf comparison. Structural unit maps disappear before coefficient
naturality is proved;the three substantive original factors are retained. -/
theorem orderedFreeSheafHomCoefficientPresheafIso_hom_app
    (X : Scheme.{u})
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (V : (FormalCoproduct.{u} X.Opens)ᵒᵖ) :
    (orderedFreeSheafHomCoefficientPresheafIso X F).hom.app V =
      (nativeAdjunctionHomPresheafIso
        (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}) F).hom.app
          (op ((orderedFreeOpenFormalPresheafFunctor X).obj V.unop)) ≫
        ((formalCoproductContravariantEvaluationIso (topOpenFreeAbelianPresheafFunctor X)
          (preadditiveYoneda.obj F.obj)).hom.app V ≫
          ((FormalCoproduct.evalOp.{u} X.Opens AddCommGrpCat.{u}).map
            (topOpenFreeAbelianPresheafHomPresheafIso X F).hom).app V) := by
  simp only [orderedFreeSheafHomCoefficientPresheafIso,Iso.trans_hom,NatTrans.comp_app,
    Functor.isoWhiskerRight_hom,Functor.isoWhiskerLeft_hom,Functor.whiskerRight_app,
    Functor.whiskerLeft_app,Functor.opComp,Iso.refl_hom,NatTrans.id_app,
    Functor.associator_hom_app,Functor.mapIso_hom,Category.id_comp,Category.assoc]
  rw [(preadditiveYoneda.obj F).map_id]
  exact Category.id_comp _
end LinearStudy
