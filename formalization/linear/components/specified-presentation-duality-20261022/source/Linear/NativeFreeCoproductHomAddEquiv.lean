module
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
universe u
/-- Native free-group Hom,with the actual generator evaluation and additive law. -/
def nativeFreeAbelianHomAddEquiv (T : Type u) (M : AddCommGrpCat.{u}) :
    (AddCommGrpCat.free.obj T ⟶ M) ≃+ (T → M) where
  toEquiv := ConcreteCategory.homEquiv.trans FreeAbelianGroup.lift.symm
  map_add' f g := by ext t; rfl
@[simp] theorem nativeFreeAbelianHomAddEquiv_apply (T : Type u) (M : AddCommGrpCat.{u})
    (f : AddCommGrpCat.free.obj T ⟶ M) (t : T) :
    nativeFreeAbelianHomAddEquiv T M f t = f (FreeAbelianGroup.of t) := rfl
/-- Hom out of an actual coproduct is the SAME family of component Homs. -/
def nativeCoproductHomAddEquiv {I : Type u} (T : I → AddCommGrpCat.{u})
    (M : AddCommGrpCat.{u}) : (∐ T ⟶ M) ≃+ (∀ i,T i ⟶ M) where
  toFun f i := Sigma.ι T i ≫ f
  invFun f := Sigma.desc f
  left_inv f := by apply Sigma.hom_ext; intro i; simp
  right_inv f := by funext i; simp
  map_add' f g := by funext i; apply comp_add
/-- Every actual coproduct/free-group generator is retained,in a common universe. -/
def nativeFreeCoproductHomAddEquiv {I : Type u} (T : I → Type u)
    (M : AddCommGrpCat.{u}) :
    (∐ (fun i => AddCommGrpCat.free.obj (T i)) ⟶ M) ≃+ ((Σ i,T i) → M) where
  toFun f x := (nativeFreeAbelianHomAddEquiv (T x.1) M)
    ((nativeCoproductHomAddEquiv (fun i => AddCommGrpCat.free.obj (T i)) M) f x.1) x.2
  invFun s := (nativeCoproductHomAddEquiv (fun i => AddCommGrpCat.free.obj (T i)) M).symm
    (fun i => (nativeFreeAbelianHomAddEquiv (T i) M).symm (fun t => s ⟨i,t⟩))
  left_inv f := by
    apply (nativeCoproductHomAddEquiv (fun i => AddCommGrpCat.free.obj (T i)) M).injective
    funext i
    simp only [AddEquiv.apply_symm_apply]
    exact (nativeFreeAbelianHomAddEquiv (T i) M).symm_apply_apply _
  right_inv s := by
    funext ⟨i,t⟩
    simp only [AddEquiv.apply_symm_apply]
  map_add' f g := by
    funext ⟨i,t⟩
    simp only [map_add,Pi.add_apply]
end LinearStudy
