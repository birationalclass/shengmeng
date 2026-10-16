module
public import Linear.TargetLinearNormal
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open scoped Matrix
variable {K : Type*} [Field K]

/-- An invertible scalar matrix changes actual ideal generators without
changing their ideal, before localization or completion. -/
theorem ideal_span_invertible_scalar_combinations
    {R β : Type*} [CommRing R] [Algebra K R] [Fintype β] [DecidableEq β]
    (M : Matrix β β K) (hM : IsUnit M.det) (G : β → R) :
    Ideal.span (Set.range (fun i => ∑ j, M i j • G j)) =
      Ideal.span (Set.range G) := by
  classical
  let H := fun i => ∑ j, M i j • G j
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Ideal.sum_mem
    intro j hj
    simpa only [Algebra.smul_def] using
      (Ideal.span (Set.range G)).mul_mem_left
        (algebraMap K R (M i j)) (Ideal.mem_span_range_self (x := j))
  · have hrecover : ∀ i, G i = ∑ j, M⁻¹ i j • H j := by
      intro i
      symm
      simp only [H, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul]
      have hh : ∀ k, (∑ j, M⁻¹ i j * M j k) = if i = k then 1 else 0 := by
        intro k
        have h := congrFun (congrFun (Matrix.nonsing_inv_mul M hM) i) k
        change (∑ j, M⁻¹ i j * M j k) = (1 : Matrix β β K) i k at h
        simpa [Matrix.one_apply] using h
      simp [hh]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [hrecover i]
    apply Ideal.sum_mem
    intro j hj
    change M⁻¹ i j • H j ∈ Ideal.span (Set.range H)
    simpa only [Algebra.smul_def] using
      (Ideal.span (Set.range H)).mul_mem_left
        (algebraMap K R (M⁻¹ i j)) (Ideal.mem_span_range_self (x := j))

theorem normalize_polynomial_normal_equations_firstOrder
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (G : β → MvPolynomial (α ⊕ β) K) (x : α ⊕ β → K)
    (h0 : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hT : ∀ i j, MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inl j) (G i)) = 0)
    (hJ : IsUnit (Matrix.det (fun i j =>
      MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i))))) :
    let J : Matrix β β K := fun i j =>
      MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i))
    let H := fun i => ∑ j, J⁻¹ i j • G j
    (∀ i, MvPolynomial.eval x (H i) = 0) ∧
    (∀ i j, MvPolynomial.eval x (MvPolynomial.pderiv j (H i)) =
      if j = Sum.inr i then 1 else 0) ∧
    Ideal.span (Set.range H) = Ideal.span (Set.range G) := by
  classical
  intro J H
  have hJi : IsUnit J⁻¹.det := Matrix.isUnit_nonsing_inv_det J hJ
  refine ⟨?_, ?_, ideal_span_invertible_scalar_combinations J⁻¹ hJi G⟩
  · intro i
    simp [H, map_sum, map_smul, h0]
  · intro i j
    cases j with
    | inl j => simp [H, map_sum, map_smul, hT]
    | inr j =>
      have h := congrFun (congrFun (Matrix.nonsing_inv_mul J hJ) i) j
      change (∑ k, J⁻¹ i k * J k j) = (1 : Matrix β β K) i j at h
      simpa [H, J, map_sum, map_smul, Matrix.one_apply, eq_comm] using h

/-- Both the ambient coordinates and actual polynomial generators are
constructed; no normal first-jet hypothesis is supplied. -/
theorem polynomial_equations_adapted_normal_generators
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (G : β → MvPolynomial (α ⊕ β) K) (x : α ⊕ β → K)
    (h0 : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j =>
      MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i))))) :
    ∃ M : Matrix (α ⊕ β) (α ⊕ β) K, Matrix.det M ≠ 0 ∧
      ∃ H : β → MvPolynomial (α ⊕ β) K,
        (∀ i, MvPolynomial.eval (M⁻¹ *ᵥ x) (H i) = 0) ∧
        (∀ i j, MvPolynomial.eval (M⁻¹ *ᵥ x) (MvPolynomial.pderiv j (H i)) =
          if j = Sum.inr i then 1 else 0) ∧
        Ideal.span (Set.range H) = Ideal.span (Set.range (fun i => polynomialLinearChange M (G i))) := by
  classical
  obtain ⟨M, hM, h0M, hTM, hNM⟩ := polynomial_equations_adapted_linear_coordinates G x h0 hJ
  have hJM : IsUnit (Matrix.det (fun i j =>
      MvPolynomial.eval (M⁻¹ *ᵥ x)
        (MvPolynomial.pderiv (Sum.inr j) (polynomialLinearChange M (G i))))) := by
    simpa only [hNM] using hJ
  obtain ⟨h0H, hDH, hideal⟩ := normalize_polynomial_normal_equations_firstOrder
    (fun i => polynomialLinearChange M (G i)) (M⁻¹ *ᵥ x) h0M hTM hJM
  exact ⟨M, hM, _, h0H, hDH, hideal⟩
end LinearStudy
