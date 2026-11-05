module
public import Linear.ProjectiveHomogeneousMultiplication
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
variable {B : Type} [CommRing B] {σ : Type}

/-- Actual polynomial multiplication, now linear also in the multiplying polynomial. -/
def projectiveHomogeneousMultiplyFamily (l m : ℕ) :
    homogeneousSubmodule σ B l →ₗ[B]
      (homogeneousSubmodule σ B m →ₗ[B] homogeneousSubmodule σ B (l+m)) where
  toFun p := projectiveHomogeneousMultiply l m p
  map_add' p q := by
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    change (p.1+q.1)*t.1 = p.1*t.1+q.1*t.1
    exact add_mul _ _ _
  map_smul' q p := by
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    change (q • p.1)*t.1 = q • (p.1*t.1)
    exact smul_mul_assoc _ _ _

/-- Reuse mathlib's linear transpose map on the ACTUAL multiplication family. -/
def projectiveHomogeneousMultiplyDualFamily (l m : ℕ) :
    homogeneousSubmodule σ B l →ₗ[B]
      (Module.Dual B (homogeneousSubmodule σ B (l+m)) →ₗ[B]
        Module.Dual B (homogeneousSubmodule σ B m)) :=
  Module.Dual.transpose.comp (projectiveHomogeneousMultiplyFamily l m)

theorem projectiveHomogeneousMultiplyDualFamily_apply (l m : ℕ)
    (p : homogeneousSubmodule σ B l) :
    projectiveHomogeneousMultiplyDualFamily l m p = projectiveHomogeneousMultiplyDual l m p := rfl

theorem projectiveHomogeneousMultiplyDual_scaled (l m : ℕ) (q : B)
    (p : homogeneousSubmodule σ B l) :
    projectiveHomogeneousMultiplyDual l m (q • p) = q • projectiveHomogeneousMultiplyDual l m p := by
  exact (projectiveHomogeneousMultiplyDualFamily l m).map_smul q p

end MvPolynomial
