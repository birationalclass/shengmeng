module
public import Linear.FirstJetNormalForm
public import Linear.PolynomialLinearChange
public import Linear.PolynomialFormalDerivative
public import Mathlib.Data.Matrix.ColumnRowPartitioned
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open scoped Matrix
variable {K α β : Type*} [Field K] [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- A unit normal minor gives an actual ambient linear shear that kills
the tangent derivative block and leaves the normal derivative block. -/
theorem normal_jacobian_linear_shear
    (A : Matrix β (α ⊕ β) K)
    (hJ : IsUnit (Matrix.det (A.submatrix id Sum.inr))) :
    let B := A.submatrix id Sum.inl
    let J := A.submatrix id Sum.inr
    let M := Matrix.fromBlocks (1 : Matrix α α K) 0 (-(J⁻¹ * B)) (1 : Matrix β β K)
    Matrix.det M = 1 ∧ A * M = Matrix.fromCols 0 J := by
  classical
  intro B J M
  have hA : A = Matrix.fromCols B J := by
    ext i j
    cases j <;> rfl
  constructor
  · simp [M]
  · rw [hA]
    change Matrix.fromCols B J * Matrix.fromBlocks 1 0 (-(J⁻¹ * B)) 1 = _
    rw [Matrix.fromCols_mul_fromBlocks]
    simp [← Matrix.mul_assoc, Matrix.mul_nonsing_inv J hJ]

/-- Adapt actual polynomial equations by an invertible ambient linear
change, deriving rather than assuming the zero tangent derivative block. -/
theorem polynomial_equations_adapted_linear_coordinates
    (G : β → MvPolynomial (α ⊕ β) K) (x : α ⊕ β → K)
    (h0 : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j =>
      MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i))))) :
    ∃ M : Matrix (α ⊕ β) (α ⊕ β) K, Matrix.det M ≠ 0 ∧
      let y := M⁻¹ *ᵥ x
      let H := fun i => polynomialLinearChange M (G i)
      (∀ i, MvPolynomial.eval y (H i) = 0) ∧
      (∀ i j, MvPolynomial.eval y (MvPolynomial.pderiv (Sum.inl j) (H i)) = 0) ∧
      (∀ i j, MvPolynomial.eval y (MvPolynomial.pderiv (Sum.inr j) (H i)) =
        MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i))) := by
  classical
  let A : Matrix β (α ⊕ β) K := fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (G i))
  let B := A.submatrix id Sum.inl
  let J := A.submatrix id Sum.inr
  let M := Matrix.fromBlocks (1 : Matrix α α K) 0 (-(J⁻¹ * B)) (1 : Matrix β β K)
  obtain ⟨hd, hAM⟩ := normal_jacobian_linear_shear A hJ
  have hM : Matrix.det M ≠ 0 := by rw [hd]; exact one_ne_zero
  refine ⟨M, hM, ?_⟩
  let y := M⁻¹ *ᵥ x
  have hxy : M *ᵥ y = x := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM),
      Matrix.one_mulVec]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [eval_polynomialLinearChange, hxy]
    exact h0 i
  · intro i j
    rw [eval_pderiv_polynomialLinearChange, hxy]
    have h := congrFun (congrFun hAM i) (Sum.inl j)
    change (∑ k, A i k * M k (Sum.inl j)) = 0 at h
    simpa only [A] using h
  · intro i j
    rw [eval_pderiv_polynomialLinearChange, hxy]
    have h := congrFun (congrFun hAM i) (Sum.inr j)
    change (∑ k, A i k * M k (Sum.inr j)) =
      MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)) at h
    simpa only [A] using h

/-- Actual polynomial target equations with a unit normal minor admit a
formal first-order normal form after an invertible ambient linear change.
The ideal of the transformed actual equations is unchanged by normalization. -/
theorem polynomial_equations_formal_firstOrder_normal_form [Nonempty β]
    (G : β → MvPolynomial (α ⊕ β) K) (x : α ⊕ β → K)
    (h0 : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j =>
      MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i))))) :
    ∃ M : Matrix (α ⊕ β) (α ⊕ β) K, Matrix.det M ≠ 0 ∧
      ∃ H : β → MvPowerSeries (α ⊕ β) K,
        (∀ i, H i - MvPowerSeries.X (Sum.inr i) ∈
          (IsLocalRing.maximalIdeal (MvPowerSeries (α ⊕ β) K)) ^ 2) ∧
        Ideal.span (Set.range H) = Ideal.span (Set.range (fun i =>
          formalPolynomialAtPoint (M⁻¹ *ᵥ x) (polynomialLinearChange M (G i)))) := by
  classical
  obtain ⟨M, hM, h0M, hTM, hNM⟩ :=
    polynomial_equations_adapted_linear_coordinates G x h0 hJ
  let y := M⁻¹ *ᵥ x
  let F := fun i => formalPolynomialAtPoint y (polynomialLinearChange M (G i))
  have h0F : ∀ i, (F i).constantCoeff = 0 := by
    intro i
    rw [formalPolynomialAtPoint_constantCoeff]
    exact h0M i
  have hTF : ∀ i j, (MvPowerSeries.pderiv (Sum.inl j) (F i)).constantCoeff = 0 := by
    intro i j
    rw [formalPolynomialAtPoint_pderiv, formalPolynomialAtPoint_constantCoeff]
    exact hTM i j
  have hNF : (fun i j => (MvPowerSeries.pderiv (Sum.inr j) (F i)).constantCoeff) =
      (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i))) := by
    funext i j
    rw [formalPolynomialAtPoint_pderiv, formalPolynomialAtPoint_constantCoeff]
    exact hNM i j
  have hJF : IsUnit (Matrix.det (fun i j =>
      (MvPowerSeries.pderiv (Sum.inr j) (F i)).constantCoeff)) := by rwa [hNF]
  obtain ⟨hfirst, hideal⟩ := normalize_formal_normal_equations_firstOrder F h0F hTF hJF
  exact ⟨M, hM, _, hfirst, hideal⟩
end LinearStudy
