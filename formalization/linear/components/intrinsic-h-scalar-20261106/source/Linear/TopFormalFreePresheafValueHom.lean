module
public import Linear.FormalCoproductCovariantEvaluation
public import Linear.NativeFormalFreeValueHom
public import Linear.OrderedFreeAbelianPresheafComplex
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
/-- The actual presheaf evaluation preserves the SAME formal coproduct. -/
def topFormalFreePresheafEvaluationIso (X : Scheme.{u}) (V : X.Opens) :
    orderedFreeOpenFormalPresheafFunctor X ⋙ (evaluation _ _).obj (op V) ≅
      (FormalCoproduct.eval.{u} X.Opens AddCommGrpCat.{u}).obj
        (topOpenFreeAbelianPresheafFunctor X ⋙ (evaluation _ _).obj (op V)) :=
  formalCoproductCovariantEvaluationIso (topOpenFreeAbelianPresheafFunctor X)
    ((evaluation _ _).obj (op V))
/-- Actual value Hom is the SAME functions on original representable generators. -/
def topFormalFreeValueHomAddEquiv (X : Scheme.{u}) (V : X.Opens) (M : AddCommGrpCat.{u})
    (U : FormalCoproduct.{u} X.Opens) :
    (((orderedFreeOpenFormalPresheafFunctor X).obj U).obj (op V) ⟶ M) ≃+
      ((Σ i : U.I,ULift.{u} (V ⟶ U.obj i)) → M) :=
  ((preadditiveYoneda.obj M).mapIso
    ((topFormalFreePresheafEvaluationIso X V).app U).symm.op).addCommGroupIsoToAddEquiv |>.trans
      (nativeFreeCoproductHomAddEquiv (fun i : U.I => ULift.{u} (V ⟶ U.obj i)) M)
/-- This ACTUAL basis identification respects EVERY formal face,not just objects. -/
theorem topFormalFreeValueHomAddEquiv_precomp (X : Scheme.{u}) (V : X.Opens)
    (M : AddCommGrpCat.{u}) {U W : FormalCoproduct.{u} X.Opens} (f : U ⟶ W)
    (h : ((orderedFreeOpenFormalPresheafFunctor X).obj W).obj (op V) ⟶ M)
    (x : Σ i : U.I,ULift.{u} (V ⟶ U.obj i)) :
    topFormalFreeValueHomAddEquiv X V M U
      (((orderedFreeOpenFormalPresheafFunctor X).map f).app (op V) ≫ h) x =
      topFormalFreeValueHomAddEquiv X V M W h ⟨f.f x.1,ULift.up (x.2.down ≫ f.φ x.1)⟩ := by
  let e := topFormalFreePresheafEvaluationIso X V
  let T : X.Opens ⥤ Type u := uliftYoneda.{u} ⋙ (evaluation _ _).obj (op V)
  let P := (FormalCoproduct.eval.{u} X.Opens AddCommGrpCat.{u}).obj (T ⋙ AddCommGrpCat.free)
  have he : (e.app U).inv ≫
      ((orderedFreeOpenFormalPresheafFunctor X).map f).app (op V) ≫ h =
        P.map f ≫ (e.app W).inv ≫ h :=
    (e.inv.naturality_assoc f h).symm
  exact (congrArg (fun q : P.obj U ⟶ M =>
    nativeFreeCoproductHomAddEquiv (fun i : U.I => T.obj (U.obj i)) M q x) he).trans
      (nativeFormalFreeValueHom_precomp T M f ((e.app W).inv ≫ h) x)
end LinearStudy
