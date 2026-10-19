module
public import Linear.FormalCoproductContravariantEvaluation
public import Linear.TopOpenFreeAbelianHomPresheaf
public import Linear.TopCechFreePresheafSimplicialIso
public import Linear.TopFreePresheafHomSheafCoefficient
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicTopology
universe u v u' v'
namespace LinearStudy
/-- Taking right opposites retains a natural isomorphism using its actual inverse. -/
def nativeRightOpIso {C : Type u} [Category.{v} C]
    {A : Type u'} [Category.{v'} A] {F G : Cᵒᵖ ⥤ A} (e : F ≅ G) :
    F.rightOp ≅ G.rightOp where
  hom := e.inv.rightOp
  inv := e.hom.rightOp
  hom_inv_id := by rw [← NatTrans.rightOp_comp,e.hom_inv_id,NatTrans.rightOp_id]
  inv_hom_id := by rw [← NatTrans.rightOp_comp,e.inv_hom_id,NatTrans.rightOp_id]

/-- The ACTUAL Hom cosimplicial object of the original free-sheaf Cech resolution
is the SAME native Cech cosimplicial object of the original coefficient presheaf. -/
def topCechFreeSheafHomCosimplicialIso (X : TopCat.{u}) {ι : Type u} (U : ι → Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (topCechFreeAbelianAugmented X U).left.rightOp ⋙ preadditiveYoneda.obj F ≅
      (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F.obj := by
  let P := topCechFreeAbelianPresheafAugmented X U
  let S := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let E := FormalCoproduct.eval.{u} (Opens X) ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
  let K := topOpenFreeAbelianPresheafFunctor X
  let YS := preadditiveYoneda.obj F
  let YP := preadditiveYoneda.obj F.obj
  let C := (FormalCoproduct.mk _ U).cech
  change (P.left ⋙ S).rightOp ⋙ YS ≅ _
  let a := Functor.isoWhiskerRight (Functor.rightOpComp P.left S) YS
  let b := Functor.associator P.left.rightOp S.op YS
  let c := Functor.isoWhiskerLeft P.left.rightOp
    (nativeAdjunctionHomPresheafIso
      (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}) F)
  let d := Functor.isoWhiskerRight (nativeRightOpIso (topCechFreePresheafSimplicialIso X U)) YP
  let e := Functor.isoWhiskerRight (Functor.rightOpComp C (E.obj K)) YP
  let f := Functor.associator C.rightOp (E.obj K).op YP
  let g := Functor.isoWhiskerLeft C.rightOp
    (formalCoproductContravariantEvaluationIso.{u} K YP)
  let h := Functor.isoWhiskerLeft C.rightOp
    ((FormalCoproduct.evalOp.{u} (Opens X) AddCommGrpCat.{u}).mapIso
      (topOpenFreeAbelianPresheafHomPresheafIso X F))
  exact a ≪≫ b ≪≫ c ≪≫ d ≪≫ e ≪≫ f ≪≫ g ≪≫ h

/-- Actual Hom cochains of the original free-sheaf resolution,with their actual
alternating coface differential. -/
def topCechFreeSheafHomComplex (X : TopCat.{u}) {ι : Type u} (U : ι → Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) : CochainComplex AddCommGrpCat.{u} ℕ :=
  (alternatingCofaceMapComplex AddCommGrpCat.{u}).obj
    ((topCechFreeAbelianAugmented X U).left.rightOp ⋙ preadditiveYoneda.obj F)

/-- The SAME Hom cochain complex is isomorphic,including all differentials,
to the original cover's native (full,not ordered) Cech complex. -/
def topCechFreeSheafHomComplexIso (X : TopCat.{u}) {ι : Type u} (U : ι → Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    topCechFreeSheafHomComplex X U F ≅ (cechComplexFunctor U).obj F.obj :=
  (alternatingCofaceMapComplex AddCommGrpCat.{u}).mapIso
    (topCechFreeSheafHomCosimplicialIso X U F)
end LinearStudy
