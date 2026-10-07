module
public import Mathlib.Algebra.Module.LinearMap.Polynomial
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open scoped Matrix

def polynomialLinearChange {K σ : Type*} [CommRing K] [Fintype σ]
    (P : Matrix σ σ K) : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  MvPolynomial.bind₁ P.toMvPolynomial

theorem polynomialLinearChange_comp {K σ : Type*} [CommRing K] [Fintype σ]
    (P Q : Matrix σ σ K) :
    (polynomialLinearChange Q).comp (polynomialLinearChange P) =
      polynomialLinearChange (P * Q) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, polynomialLinearChange, MvPolynomial.bind₁_X_right]
  exact (Matrix.toMvPolynomial_mul P Q i).symm

theorem polynomialLinearChange_one {K σ : Type*} [CommRing K] [Fintype σ]
    [DecidableEq σ] : polynomialLinearChange (1 : Matrix σ σ K) = AlgHom.id K _ := by
  rw [polynomialLinearChange, Matrix.toMvPolynomial_one, MvPolynomial.bind₁_X_left]

def polynomialLinearChangeEquiv {K σ : Type*} [Field K] [Fintype σ]
    [DecidableEq σ] (P : Matrix σ σ K) (hP : Matrix.det P ≠ 0) :
    MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K :=
  AlgEquiv.ofAlgHom (polynomialLinearChange P) (polynomialLinearChange P⁻¹)
    (by rw [polynomialLinearChange_comp, Matrix.nonsing_inv_mul P
          (isUnit_iff_ne_zero.mpr hP), polynomialLinearChange_one])
    (by rw [polynomialLinearChange_comp, Matrix.mul_nonsing_inv P
          (isUnit_iff_ne_zero.mpr hP), polynomialLinearChange_one])

theorem eval_polynomialLinearChange {K σ : Type*} [CommRing K] [Fintype σ]
    (P : Matrix σ σ K) (y : σ → K) (G : MvPolynomial σ K) :
    MvPolynomial.eval y (polynomialLinearChange P G) =
      MvPolynomial.eval (P *ᵥ y) G := by
  have h : (MvPolynomial.aeval (R := K) y).comp (polynomialLinearChange P) =
      MvPolynomial.aeval (R := K) (P *ᵥ y) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [polynomialLinearChange, Matrix.toMvPolynomial_eval_eq_apply]
  exact DFunLike.congr_fun h G

theorem pderiv_matrix_linear_polynomial {K σ : Type*} [CommRing K] [Fintype σ]
    (P : Matrix σ σ K) (i j : σ) :
    MvPolynomial.pderiv j (P.toMvPolynomial i) = MvPolynomial.C (P i j) := by
  classical
  simp [Matrix.toMvPolynomial, ← MvPolynomial.C_mul_X_eq_monomial,
    MvPolynomial.pderiv_X, Pi.single_apply, eq_comm]

theorem pderiv_polynomialLinearChange {K σ : Type*} [CommRing K] [Fintype σ]
    (P : Matrix σ σ K) (G : MvPolynomial σ K) (j : σ) :
    MvPolynomial.pderiv j (polynomialLinearChange P G) =
      ∑ i, MvPolynomial.C (P i j) *
        polynomialLinearChange P (MvPolynomial.pderiv i G) := by
  classical
  induction G using MvPolynomial.induction_on with
  | C a => simp [polynomialLinearChange]
  | add G H hG hH =>
      simp only [map_add, hG, hH, mul_add, Finset.sum_add_distrib]
  | mul_X G i hG =>
      simp only [polynomialLinearChange] at hG
      simp only [map_mul, MvPolynomial.pderiv_mul, polynomialLinearChange,
        MvPolynomial.bind₁_X_right, pderiv_matrix_linear_polynomial, hG,
        MvPolynomial.pderiv_X, Pi.single_apply, map_add, map_mul]
      simp [Finset.sum_add_distrib, Finset.mul_sum, mul_add, mul_comm, mul_left_comm]

theorem eval_pderiv_polynomialLinearChange {K σ : Type*} [CommRing K] [Fintype σ]
    (P : Matrix σ σ K) (G : MvPolynomial σ K) (y : σ → K) (j : σ) :
    MvPolynomial.eval y (MvPolynomial.pderiv j (polynomialLinearChange P G)) =
      ∑ i, MvPolynomial.eval (P *ᵥ y) (MvPolynomial.pderiv i G) * P i j := by
  rw [pderiv_polynomialLinearChange]
  simp [eval_polynomialLinearChange, mul_comm]

end LinearStudy
