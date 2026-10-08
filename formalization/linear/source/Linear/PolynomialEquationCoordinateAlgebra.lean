module
public import Linear.PolynomialLinearChange
public import Linear.PolynomialFiberJacobian
public import Mathlib.RingTheory.Finiteness.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open scoped Matrix

theorem ideal_span_matrix_polynomial_combination_le
    {K R τ : Type*} [Field K] [CommRing R] [Algebra K R] [Fintype τ]
    (M : Matrix τ τ K) (p : τ → R) :
    Ideal.span (Set.range (fun i => MvPolynomial.aeval p (M.toMvPolynomial i))) ≤
      Ideal.span (Set.range p) := by
  classical
  apply Ideal.span_le.mpr
  rintro F ⟨i,rfl⟩
  simp only [Matrix.toMvPolynomial, ← MvPolynomial.C_mul_X_eq_monomial, map_sum,
    map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  exact Ideal.sum_mem _ (fun j _ => Ideal.mul_mem_left _ _
    (Ideal.subset_span (Set.mem_range_self j)))

/-- Invertible target linear combinations preserve the actual equation
ideal, including its normal nilpotents, not merely its zero set. -/
theorem ideal_span_invertible_matrix_polynomial_combination
    {K R τ : Type*} [Field K] [CommRing R] [Algebra K R] [Fintype τ] [DecidableEq τ]
    (M : Matrix τ τ K) (hM : Matrix.det M ≠ 0) (p : τ → R) :
    Ideal.span (Set.range (fun i => MvPolynomial.aeval p ((M⁻¹).toMvPolynomial i))) =
      Ideal.span (Set.range p) := by
  let q := fun i => MvPolynomial.aeval p ((M⁻¹).toMvPolynomial i)
  have hHom : MvPolynomial.aeval q = (MvPolynomial.aeval p).comp (polynomialLinearChange M⁻¹) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [q,polynomialLinearChange]
  have hcomp : (polynomialLinearChange M⁻¹).comp (polynomialLinearChange M) = AlgHom.id K _ := by
    rw [polynomialLinearChange_comp,Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM),
      polynomialLinearChange_one]
  have hUndo : (fun i => MvPolynomial.aeval q (M.toMvPolynomial i)) = p := by
    funext i
    rw [hHom]
    change MvPolynomial.aeval p (polynomialLinearChange M⁻¹ (M.toMvPolynomial i)) = p i
    have h := AlgHom.congr_fun hcomp (MvPolynomial.X i)
    simp only [AlgHom.comp_apply,polynomialLinearChange,MvPolynomial.bind₁_X_right,
      AlgHom.id_apply] at h
    change polynomialLinearChange M⁻¹ (M.toMvPolynomial i) = MvPolynomial.X i at h
    rw [h]
    simp
  apply le_antisymm
  · exact ideal_span_matrix_polynomial_combination_le M⁻¹ p
  · have h := ideal_span_matrix_polynomial_combination_le M q
    rw [hUndo] at h
    exact h

/-- Source polynomial coordinates, independent target indexing and an
invertible target matrix preserve finiteness of the ACTUAL equation algebra. -/
theorem polynomial_equation_coordinate_algebra_finite
    {K σ τ : Type*} [Field K] [Fintype τ] [DecidableEq τ]
    (E : MvPolynomial σ K ≃ₐ[K] MvPolynomial τ K) (b : σ ≃ τ)
    (M : Matrix τ τ K) (hM : Matrix.det M ≠ 0) (P : σ → MvPolynomial σ K)
    [Module.Finite K (MvPolynomial σ K ⧸ Ideal.span (Set.range P))] :
    Module.Finite K (MvPolynomial τ K ⧸ Ideal.span (Set.range (fun i =>
      MvPolynomial.aeval (fun j => E (P (b.symm j))) ((M⁻¹).toMvPolynomial i)))) := by
  let p := fun j => E (P (b.symm j))
  have hRange : Set.range p = E '' Set.range P := by
    ext F
    constructor
    · rintro ⟨j,rfl⟩
      exact ⟨P (b.symm j),Set.mem_range_self _,rfl⟩
    · rintro ⟨F,⟨i,rfl⟩,rfl⟩
      exact ⟨b i,by simp [p]⟩
  have hIdeal : Ideal.span (Set.range p) = (Ideal.span (Set.range P)).map E.toRingHom := by
    rw [Ideal.map_span]
    exact congrArg Ideal.span hRange
  let eqv := Ideal.quotientEquivAlg (Ideal.span (Set.range P)) (Ideal.span (Set.range p)) E hIdeal
  have hfin : Module.Finite K (MvPolynomial τ K ⧸ Ideal.span (Set.range p)) :=
    Module.Finite.equiv eqv.toLinearEquiv
  rw [ideal_span_invertible_matrix_polynomial_combination M hM p]
  exact hfin

theorem matrix_polynomial_centered_numerators
    {K R τ : Type*} [Field K] [CommRing R] [Algebra K R] [Fintype τ]
    (M : Matrix τ τ K) (y : τ → K) (p0 : R) (p : τ → R) :
    (fun i => MvPolynomial.aeval p (M.toMvPolynomial i) -
      algebraMap K R ((M *ᵥ y) i) * p0) =
      (fun i => MvPolynomial.aeval (fun j => p j - algebraMap K R (y j) * p0)
        (M.toMvPolynomial i)) := by
  classical
  funext i
  simp only [Matrix.toMvPolynomial, ← MvPolynomial.C_mul_X_eq_monomial, map_sum,
    map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Matrix.mulVec, dotProduct,
    mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, mul_assoc]

end LinearStudy
