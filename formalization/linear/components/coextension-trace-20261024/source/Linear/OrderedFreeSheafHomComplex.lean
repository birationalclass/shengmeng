module
public import Linear.OrderedFreeSheafCechResolution
public import Linear.OrderedFormalHomCochainIso
public import Linear.TopFreePresheafHomSheafCoefficient
public import Linear.FormalCoproductContravariantEvaluation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
/-- The original ORDERED Cech complex of the SAME actual abelian-sheaf coefficients. -/
def orderedTopAbelianCechComplex (X : Scheme.{u}) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (F : TopCat.Sheaf AddCommGrpCat.{u} X) : CochainComplex AddCommGrpCat.{u} ℕ :=
  orderedFormalCechComplex ((FormalCoproduct.evalOp.{u} X.Opens AddCommGrpCat.{u}).obj F.obj) U
/-- The actual Hom complex of the actual ordered free-SHEAF resolution is the SAME
ordered coefficient Cech complex,with every original differential and sign. -/
def orderedFreeSheafActualHomComplexIso (X : Scheme.{u}) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    chainActualHomCochain (orderedFreeAbelianSheafComplex X U) F ≅
      orderedTopAbelianCechComplex X U F := by
  let P := orderedFreeOpenFormalPresheafFunctor X
  let K := topOpenFreeAbelianPresheafFunctor X
  let S := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let YS := preadditiveYoneda.obj F
  let YP := preadditiveYoneda.obj F.obj
  let a := Functor.isoWhiskerRight (Functor.opComp P S) YS
  let b := Functor.associator P.op S.op YS
  let c := Functor.isoWhiskerLeft P.op (nativeAdjunctionHomPresheafIso
    (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}) F)
  let d := formalCoproductContravariantEvaluationIso.{u} K YP
  let e := (FormalCoproduct.evalOp.{u} X.Opens AddCommGrpCat.{u}).mapIso
    (topOpenFreeAbelianPresheafHomPresheafIso X F)
  exact actualHomSourceComplexIso (orderedCovariantWhiskeringChainIso U P S) F ≪≫
    orderedFormalActualHomCochainIso U (P ⋙ S) F ≪≫
      orderedFormalCechComplexIso U (a ≪≫ b ≪≫ c ≪≫ d ≪≫ e)
end LinearStudy
