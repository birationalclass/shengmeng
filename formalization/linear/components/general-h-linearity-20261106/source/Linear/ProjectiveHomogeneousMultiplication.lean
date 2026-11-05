module
public import Linear.ProjectiveGeneralResidueDuality
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
variable {R : Type} {σ : Type} [CommRing R]

/-- Multiplication in the actual polynomial ring, restricted to homogeneous pieces.
No duality transport is used to define this map. -/
def projectiveHomogeneousMultiply (l m : ℕ)
    (p : homogeneousSubmodule σ R l) :
    homogeneousSubmodule σ R m →ₗ[R] homogeneousSubmodule σ R (l+m) where
  toFun q := ⟨p.1*q.1, homogeneousSubmodule_mul l m
    (Submodule.mul_mem_mul p.property q.property)⟩
  map_add' q s := by apply Subtype.ext; exact mul_add _ _ _
  map_smul' r q := by apply Subtype.ext; exact mul_smul_comm _ _ _

/-- The underlying polynomial of the multiplication map is the actual product. -/
theorem projectiveHomogeneousMultiply_coe (l m : ℕ)
    (p : homogeneousSubmodule σ R l) (q : homogeneousSubmodule σ R m) :
    (projectiveHomogeneousMultiply l m p q).1 = p.1*q.1 := rfl

/-- The dual map is precomposition with actual polynomial multiplication.
Its identification with native twist multiplication remains a separate obligation. -/
def projectiveHomogeneousMultiplyDual (l m : ℕ)
    (p : homogeneousSubmodule σ R l) :
    Module.Dual R (homogeneousSubmodule σ R (l+m)) →ₗ[R]
      Module.Dual R (homogeneousSubmodule σ R m) :=
  LinearMap.dualMap (projectiveHomogeneousMultiply l m p)

theorem projectiveHomogeneousMultiplyDual_apply (l m : ℕ)
    (p : homogeneousSubmodule σ R l)
    (v : Module.Dual R (homogeneousSubmodule σ R (l+m)))
    (q : homogeneousSubmodule σ R m) :
    projectiveHomogeneousMultiplyDual l m p v q =
      v (projectiveHomogeneousMultiply l m p q) := rfl
end MvPolynomial
