module
public import Linear.FormalCoproductFunctorMap
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
open CategoryTheory CategoryTheory.Limits Opposite
universe w u v u' v' u'' v''
namespace LinearStudy
variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  {B : Type u''} [Category.{v''} B]
  [HasCoproducts.{w} A] [HasProducts.{w} B]
  (K : C ⥤ A) (H : Aᵒᵖ ⥤ B) [∀ (α : Type w),PreservesLimitsOfShape (Discrete α) H]
/-- Native opposite-coproduct and preserved-product isomorphisms,without replacing
actual coproducts or products by an arbitrary coordinate model. -/
def formalCoproductContravariantComponentIso (U : FormalCoproduct.{w} C) :
    H.obj (op (∐ (K.obj ∘ U.obj))) ≅
      ∏ᶜ (fun i : U.I => H.obj (op (K.obj (U.obj i)))) :=
  H.mapIso (opCoproductIsoProduct (K.obj ∘ U.obj)) ≪≫
    PreservesProduct.iso H (fun i : U.I => op (K.obj (U.obj i)))

@[reassoc (attr := simp)]
theorem formalCoproductContravariantComponentIso_hom_π
    (U : FormalCoproduct.{w} C) (i : U.I) :
    (formalCoproductContravariantComponentIso K H U).hom ≫
      Pi.π (fun j : U.I => H.obj (op (K.obj (U.obj j)))) i =
      H.map ((Sigma.ι (K.obj ∘ U.obj) i).op) := by
  simp only [formalCoproductContravariantComponentIso,Iso.trans_hom,
    Category.assoc,Functor.mapIso_hom,PreservesProduct.iso_hom,piComparison_comp_π]
  rw [← H.map_comp]
  simpa only [Function.comp_def] using
    congrArg H.map (opCoproductIsoProduct_hom_comp_π (Z := K.obj ∘ U.obj) i)

/-- Contravariant evaluation of the actual formal coproduct functor is the SAME
native formal-product evaluation,including all original maps. -/
def formalCoproductContravariantEvaluationIso :
    ((FormalCoproduct.eval C A).obj K).op ⋙ H ≅
      (FormalCoproduct.evalOp C B).obj (K.op ⋙ H) :=
  NatIso.ofComponents (fun U => formalCoproductContravariantComponentIso K H U.unop)
    (fun {U V} f => by
      apply Pi.hom_ext
      intro i
      dsimp [FormalCoproduct.eval,FormalCoproduct.evalOp]
      simp only [Category.assoc,Function.comp_def,
        formalCoproductContravariantComponentIso_hom_π,Pi.lift_comp_π]
      simp only [← H.map_comp,← op_comp,Sigma.ι_comp_desc]
      rw [← Category.assoc,formalCoproductContravariantComponentIso_hom_π]
      rw [← H.map_comp,← op_comp]
      rfl)
end LinearStudy
