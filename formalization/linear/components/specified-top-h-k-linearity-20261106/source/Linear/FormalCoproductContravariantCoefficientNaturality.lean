module
public import Linear.FormalCoproductContravariantEvaluation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits Opposite
universe w u v u' v' u'' v''
variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  {B : Type u''} [Category.{v''} B] [HasCoproducts.{w} A] [HasProducts.{w} B]
  (K : C ⥤ A) (H₁ H₂ : Aᵒᵖ ⥤ B)
  [∀ (α : Type w),PreservesLimitsOfShape (Discrete α) H₁]
  [∀ (α : Type w),PreservesLimitsOfShape (Discrete α) H₂]
/-- Native actual Hom-of-coproduct/product comparison preserves actual
coefficient transformations,proved on original coproduct inclusions. -/
theorem formalCoproductContravariantComponentIso_coefficient_naturality
    (a : H₁ ⟶ H₂) (U : FormalCoproduct.{w} C) :
    a.app (op (∐ (K.obj ∘ U.obj))) ≫
      (formalCoproductContravariantComponentIso K H₂ U).hom =
      (formalCoproductContravariantComponentIso K H₁ U).hom ≫
        CategoryTheory.Limits.Pi.map (fun i : U.I => a.app (op (K.obj (U.obj i)))) := by
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc,CategoryTheory.Limits.Pi.map_π]
  rw [formalCoproductContravariantComponentIso_hom_π,← Category.assoc,
    formalCoproductContravariantComponentIso_hom_π]
  exact (a.naturality (Sigma.ι (K.obj ∘ U.obj) i).op).symm
/-- The SAME formal-coproduct evaluation natural isomorphism is natural
in coefficients,including ALL formal coproduct maps. -/
theorem formalCoproductContravariantEvaluationIso_coefficient_naturality
    (a : H₁ ⟶ H₂) :
    Functor.whiskerLeft ((FormalCoproduct.eval C A).obj K).op a ≫
      (formalCoproductContravariantEvaluationIso K H₂).hom =
      (formalCoproductContravariantEvaluationIso K H₁).hom ≫
        (FormalCoproduct.evalOp C B).map (Functor.whiskerLeft K.op a) := by
  ext U
  exact formalCoproductContravariantComponentIso_coefficient_naturality K H₁ H₂ a U.unop
end LinearStudy
