module
public import Linear.FormalCoproductContravariantEvaluation
public import Linear.FormalCechFormalEvaluation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
universe w u v u' v' u'' v''
variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  {B : Type u''} [Category.{v''} B]
  [HasCoproducts.{w} A] [HasCoproducts.{w} B]
  (K : C ⥤ A) (H : A ⥤ B) [∀ (α : Type w),PreservesColimitsOfShape (Discrete α) H]
@[reassoc (attr := simp)]
theorem formalCoproductCovariant_map_ι_hom (U : FormalCoproduct.{w} C) (i : U.I) :
    H.map (Sigma.ι (fun j => K.obj (U.obj j)) i) ≫ (PreservesCoproduct.iso H (fun j => K.obj (U.obj j))).hom =
      Sigma.ι (fun j => H.obj (K.obj (U.obj j))) i := by
  apply (cancel_mono (PreservesCoproduct.iso H (fun j => K.obj (U.obj j))).inv).1
  simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
  simp only [PreservesCoproduct.inv_hom,ι_comp_sigmaComparison]
/-- Actual formal coproduct evaluation commutes with a coproduct-preserving functor,
including every original component map. -/
def formalCoproductCovariantEvaluationIso :
    (FormalCoproduct.eval.{w} C A).obj K ⋙ H ≅
      (FormalCoproduct.eval.{w} C B).obj (K ⋙ H) :=
  (FormalCoproduct.evalObjCompIso K H).symm
end LinearStudy
