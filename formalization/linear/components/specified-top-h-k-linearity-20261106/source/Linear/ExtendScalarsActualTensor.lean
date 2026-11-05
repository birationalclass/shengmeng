module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.TensorProduct.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory TensorProduct
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Identity on actual elements; compares the categorical restricted-scalar
module with the original algebra's scalar action. -/
def restrictedAlgebraModuleEquiv :
    ((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) ≃ₗ[R] S where
  toFun := fun x => x
  invFun := fun x => x
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun r x => by
    simp [ModuleCat.restrictScalars.smul_def,Algebra.smul_def]

/-- An actual carrier equivalence, rather than an assumed identification,
between category-theoretic extension of scalars and the algebra tensor. -/
def extendScalarsActualTensorAddEquiv (M : ModuleCat.{u} R) :
    ((ModuleCat.extendScalars (algebraMap R S)).obj M) ≃+ S ⊗[R] M :=
  (TensorProduct.congr restrictedAlgebraModuleEquiv (LinearEquiv.refl R M)).toAddEquiv

theorem extendScalarsActualTensor_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (f.hom.baseChange S) ∘ extendScalarsActualTensorAddEquiv (S := S) M=
    extendScalarsActualTensorAddEquiv (S := S) N ∘
      ((ModuleCat.extendScalars (algebraMap R S)).map f) := by
  funext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => rfl
  | add x y hx hy =>
    simp only [Function.comp_apply] at hx hy ⊢
    simp only [map_add,hx,hy]

end LinearStudy
