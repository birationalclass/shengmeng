module
public import Linear.FormalProductEvaluationWhiskering
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits Opposite
universe w u v u' v' u'' v''
variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  {B : Type u''} [Category.{v''} B] [HasProducts.{w} A] [HasProducts.{w} B]
/-- The native product-preservation isomorphism is natural in the actual
coefficient family map,derived on ORIGINAL product projections. -/
theorem preservesProductIso_coefficient_naturality {J : Type w}
    (H : A ⥤ B) [PreservesLimitsOfShape (Discrete J) H]
    {P Q : J → A} (a : ∀ j,P j ⟶ Q j) :
    H.map (CategoryTheory.Limits.Pi.map a) ≫ (PreservesProduct.iso H Q).hom =
      (PreservesProduct.iso H P).hom ≫ CategoryTheory.Limits.Pi.map (fun j => H.map (a j)) := by
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc,PreservesProduct.iso_hom,piComparison_comp_π,CategoryTheory.Limits.Pi.map_π]
  rw [← H.map_comp,CategoryTheory.Limits.Pi.map_π,H.map_comp]
  rw [← Category.assoc,piComparison_comp_π]
/-- The SAME original formal-product-evaluation/forgetting comparison
is natural in the ORIGINAL coefficient-presheaf transformation. -/
theorem formalProductEvaluationWhiskeringIso_coefficient_naturality
    {T T' : Cᵒᵖ ⥤ A} (a : T ⟶ T') (H : A ⥤ B)
    [∀ (J : Type w),PreservesLimitsOfShape (Discrete J) H] :
    Functor.whiskerRight ((FormalCoproduct.evalOp.{w} C A).map a) H ≫
        (formalProductEvaluationWhiskeringIso T' H).hom =
      (formalProductEvaluationWhiskeringIso T H).hom ≫
        (FormalCoproduct.evalOp.{w} C B).map (Functor.whiskerRight a H) := by
  ext U
  exact preservesProductIso_coefficient_naturality H
    (fun i => a.app (op (U.unop.obj i)))
end LinearStudy
