module
public import Linear.FormalCoproductContravariantEvaluation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000
set_option backward.defeqAttrib.useBackward true
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits Opposite
universe w u v u' v' u'' v''
variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  {B : Type u''} [Category.{v''} B] [HasProducts.{w} A] [HasProducts.{w} B]
  (T : Cᵒᵖ ⥤ A) (H : A ⥤ B) [∀ (J : Type w),PreservesLimitsOfShape (Discrete J) H]
@[reassoc (attr := simp)]
theorem formalProductEvaluation_component_hom_π (U : FormalCoproduct.{w} C) (i : U.I) :
    (PreservesProduct.iso H (fun j => T.obj (op (U.obj j)))).hom ≫
      Pi.π (fun j => H.obj (T.obj (op (U.obj j)))) i =
        H.map (Pi.π (fun j => T.obj (op (U.obj j))) i) := by
  simp only [PreservesProduct.iso_hom,piComparison_comp_π]
/-- Actual formal PRODUCT evaluation commutes with product-preserving coefficient
functors,including all original component maps. -/
def formalProductEvaluationWhiskeringIso :
    (FormalCoproduct.evalOp.{w} C A).obj T ⋙ H ≅
      (FormalCoproduct.evalOp.{w} C B).obj (T ⋙ H) :=
  NatIso.ofComponents (fun U => PreservesProduct.iso H (fun i => T.obj (op (U.unop.obj i))))
    (fun {U V} f => by
      change H.map (Pi.lift (fun j => Pi.π (fun k => T.obj (op (U.unop.obj k))) (f.unop.f j) ≫
        T.map (f.unop.φ j).op)) ≫
          (PreservesProduct.iso H (fun j => T.obj (op (V.unop.obj j)))).hom =
        (PreservesProduct.iso H (fun j => T.obj (op (U.unop.obj j)))).hom ≫
          Pi.lift (fun j => Pi.π (fun k => H.obj (T.obj (op (U.unop.obj k)))) (f.unop.f j) ≫
            H.map (T.map (f.unop.φ j).op))
      apply Pi.hom_ext
      intro i
      simp only [Category.assoc,PreservesProduct.iso_hom,piComparison_comp_π,Pi.lift_comp_π]
      rw [← H.map_comp,Pi.lift_comp_π,H.map_comp]
      rw [← Category.assoc,piComparison_comp_π])
end LinearStudy
