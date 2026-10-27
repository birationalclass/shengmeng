module
public import Linear.IntegerGradedHomPrecomposition
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Grp.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 5000
namespace LinearStudy
variable {K S M N : Type} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M]
variable [AddCommGroup N] [Module K N] [Module S N]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (D : ℤ → Submodule K M) (E : ℤ → Submodule K N)
variable (e : M →ₗ[S] N)
variable (he : ∀ t : ℤ, ∀ x : M, x ∈ D t → e x ∈ E t)

open CategoryTheory
/-- The original covariant K-dual of graded-Hom precomposition,as an actual abelian-group morphism. -/
def integerGradedHomDualCoefficientHom (d : ℤ) :
    (forget₂ (ModuleCat K) AddCommGrpCat).obj (ModuleCat.of K (Module.Dual K (integerGradedHomPiece B D d))) ⟶
    (forget₂ (ModuleCat K) AddCommGrpCat).obj (ModuleCat.of K (Module.Dual K (integerGradedHomPiece B E d))) :=
  (forget₂ (ModuleCat K) AddCommGrpCat).map
    (ModuleCat.ofHom (integerGradedHomPrecomposition B D E e he d).dualMap)
/-- Exact original value lambda(phi composed with e). -/
theorem integerGradedHomDualCoefficientHom_apply (d : ℤ)
    (ell : Module.Dual K (integerGradedHomPiece B D d)) (phi : integerGradedHomPiece B E d) :
    (show Module.Dual K (integerGradedHomPiece B E d) from
      integerGradedHomDualCoefficientHom B D E e he d ell) phi =
      ell (integerGradedHomPrecomposition B D E e he d phi) := rfl
end LinearStudy
