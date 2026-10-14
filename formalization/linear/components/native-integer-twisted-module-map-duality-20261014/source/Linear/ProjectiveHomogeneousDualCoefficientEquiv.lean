module
public import Linear.ProjectiveHomogeneousCoefficientEquiv
public import Mathlib.Algebra.Module.Equiv.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace MvPolynomial
variable {R S : Type} [CommRing R] [CommRing S] {σ : Type}
attribute [local instance] projectiveCoefficientInverseForward projectiveCoefficientInverseBackward

/-- Change ORIGINAL dual functional coefficients by mathlib arrowCongr,
using the constructed original homogeneous equivalence and the original
ring equivalence. No dual comparison is supplied as an input. -/
def projectiveHomogeneousDualCoefficientEquiv (e : R ≃+* S) (m : ℕ) :
    Module.Dual R (homogeneousSubmodule σ R m) ≃ₛₗ[e.toRingHom]
      Module.Dual S (homogeneousSubmodule σ S m) :=
  LinearEquiv.arrowCongr (projectiveHomogeneousCoefficientEquiv e m) e.toSemilinearEquiv

/-- The dual functional is the original functional on the ORIGINAL
inverse homogeneous coefficient map,followed by the original ring map. -/
theorem projectiveHomogeneousDualCoefficientEquiv_apply (e : R ≃+* S) (m : ℕ)
    (φ : Module.Dual R (homogeneousSubmodule σ R m)) (q : homogeneousSubmodule σ S m) :
    projectiveHomogeneousDualCoefficientEquiv e m φ q =
      e (φ ((projectiveHomogeneousCoefficientEquiv e m).symm q)) := rfl

/-- The ACTUAL original multiplication transpose commutes with the
constructed dual coefficient change. This is a proved entry square,
not a new cohomology or graded-matrix comparison premise. -/
theorem projectiveHomogeneousDualCoefficientEquiv_multiply (e : R ≃+* S) (l m : ℕ)
    (p : homogeneousSubmodule σ R l)
    (φ : Module.Dual R (homogeneousSubmodule σ R (l+m))) :
    projectiveHomogeneousDualCoefficientEquiv e m (projectiveHomogeneousMultiplyDual l m p φ) =
      projectiveHomogeneousMultiplyDual l m (projectiveHomogeneousCoefficientEquiv e l p)
        (projectiveHomogeneousDualCoefficientEquiv e (l+m) φ) := by
  apply LinearMap.ext
  intro q
  change e (φ (projectiveHomogeneousMultiply l m p
      ((projectiveHomogeneousCoefficientEquiv e m).symm q))) =
    e (φ ((projectiveHomogeneousCoefficientEquiv e (l+m)).symm
      (projectiveHomogeneousMultiply l m (projectiveHomogeneousCoefficientEquiv e l p) q)))
  apply congrArg e
  apply congrArg φ
  apply (projectiveHomogeneousCoefficientEquiv e (l+m)).injective
  rw [projectiveHomogeneousCoefficientEquiv_multiply,LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

end MvPolynomial
