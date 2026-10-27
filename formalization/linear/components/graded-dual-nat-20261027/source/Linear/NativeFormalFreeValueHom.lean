module
public import Linear.FormalCoproductCovariantEvaluation
public import Linear.NativeFreeCoproductHomAddEquiv
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
universe u v w z
@[simp] theorem nativeFreeCoproductHomAddEquiv_apply {I : Type u} (T : I → Type u)
    (M : AddCommGrpCat.{u}) (h : ∐ (fun i => AddCommGrpCat.free.obj (T i)) ⟶ M)
    (x : Σ i,T i) : nativeFreeCoproductHomAddEquiv T M h x =
      (Sigma.ι (fun i => AddCommGrpCat.free.obj (T i)) x.1 ≫ h) (FreeAbelianGroup.of x.2) := rfl
/-- The native formal-coproduct map on each original component. -/
@[reassoc (attr := simp)]
theorem nativeFormalEval_ι_map {C : Type v} [Category.{w} C]
    {A : Type z} [Category.{u} A] [HasCoproducts.{u} A]
    (K : C ⥤ A) {U W : FormalCoproduct.{u} C} (f : U ⟶ W) (i : U.I) :
    Sigma.ι (fun j => K.obj (U.obj j)) i ≫ ((FormalCoproduct.eval.{u} C A).obj K).map f =
      K.map (f.φ i) ≫ Sigma.ι (fun j => K.obj (W.obj j)) (f.f i) :=
  Sigma.ι_comp_desc _ _
/-- Native free/coproduct Hom respects every ORIGINAL formal-component map. -/
theorem nativeFormalFreeValueHom_precomp {C : Type v} [Category.{w} C]
    (T : C ⥤ Type u) (M : AddCommGrpCat.{u})
    {U W : FormalCoproduct.{u} C} (f : U ⟶ W)
    (h : ((FormalCoproduct.eval.{u} C AddCommGrpCat.{u}).obj (T ⋙ AddCommGrpCat.free)).obj W ⟶ M)
    (x : Σ i : U.I,T.obj (U.obj i)) :
    nativeFreeCoproductHomAddEquiv (fun i : U.I => T.obj (U.obj i)) M
      (((FormalCoproduct.eval.{u} C AddCommGrpCat.{u}).obj (T ⋙ AddCommGrpCat.free)).map f ≫ h) x =
      nativeFreeCoproductHomAddEquiv (fun i : W.I => T.obj (W.obj i)) M h
        ⟨f.f x.1,T.map (f.φ x.1) x.2⟩ := by
  let P := (FormalCoproduct.eval.{u} C AddCommGrpCat.{u}).obj (T ⋙ AddCommGrpCat.free)
  have hf := nativeFormalEval_ι_map (T ⋙ AddCommGrpCat.free) f x.1
  have hg := congrArg (fun q : AddCommGrpCat.free.obj (T.obj (U.obj x.1)) ⟶ P.obj W => q ≫ h) hf
  have hv := ConcreteCategory.congr_hom hg (FreeAbelianGroup.of x.2)
  change h ((P.map f) ((Sigma.ι (fun j => AddCommGrpCat.free.obj (T.obj (U.obj j))) x.1)
      (FreeAbelianGroup.of x.2))) =
    h ((Sigma.ι (fun j => AddCommGrpCat.free.obj (T.obj (W.obj j))) (f.f x.1))
      (FreeAbelianGroup.of (T.map (f.φ x.1) x.2)))
  change h ((P.map f) ((Sigma.ι (fun j => AddCommGrpCat.free.obj (T.obj (U.obj j))) x.1)
      (FreeAbelianGroup.of x.2))) =
    h ((Sigma.ι (fun j => AddCommGrpCat.free.obj (T.obj (W.obj j))) (f.f x.1))
      (FreeAbelianGroup.map (T.map (f.φ x.1)) (FreeAbelianGroup.of x.2))) at hv
  rw [FreeAbelianGroup.map_of_apply] at hv
  exact hv
end LinearStudy
