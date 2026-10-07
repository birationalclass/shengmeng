module
public import Linear.FormalFirstOrder
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open scoped Matrix
variable {K σ : Type*} [Field K] [Fintype σ] [DecidableEq σ] [Nonempty σ]

/-- Vanishing of the actual constant and all derivative constants gives
membership in the square of the actual maximal ideal. -/
theorem powerSeries_zero_firstJet_mem_square
    (F : MvPowerSeries σ K) (h0 : F.constantCoeff = 0)
    (hD : ∀ j, (MvPowerSeries.pderiv j F).constantCoeff = 0) :
    F ∈ (IsLocalRing.maximalIdeal (MvPowerSeries σ K)) ^ 2 := by
  classical
  obtain ⟨a, ha⟩ := powerSeries_zeroConstant_variable_expansion F h0
  have hac : ∀ j, (a j).constantCoeff = 0 := by
    intro j
    have h := congrArg (fun H : MvPowerSeries σ K =>
      (MvPowerSeries.pderiv j H).constantCoeff) ha
    simpa [hD j, map_sum, Derivation.leibniz, MvPowerSeries.pderiv_X,
      Pi.single_apply, apply_ite] using h.symm
  rw [ha, pow_two]
  apply Ideal.sum_mem
  intro i hi
  apply Ideal.mul_mem_mul
  · rw [powerSeries_maximalIdeal_eq_constantCoeff_kernel]
    exact hac i
  · rw [powerSeries_maximalIdeal_eq_constantCoeff_kernel]
    exact MvPowerSeries.constantCoeff_X i

theorem powerSeries_firstJet_equal_iff_square
    (F G : MvPowerSeries σ K) :
    F - G ∈ (IsLocalRing.maximalIdeal (MvPowerSeries σ K)) ^ 2 ↔
      F.constantCoeff = G.constantCoeff ∧
        ∀ j, (MvPowerSeries.pderiv j F).constantCoeff =
          (MvPowerSeries.pderiv j G).constantCoeff := by
  constructor
  · intro h
    exact ⟨powerSeries_firstOrder_constantCoeff F G h,
      fun j => powerSeries_firstOrder_derivative_constantCoeff F G j h⟩
  · rintro ⟨h0, hD⟩
    apply powerSeries_zero_firstJet_mem_square
    · simpa only [map_sub, sub_eq_zero] using h0
    · intro j
      simpa only [map_sub, sub_eq_zero] using hD j

theorem normal_firstOrder_of_derivative_coordinates
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Nonempty β]
    (H : β → MvPowerSeries (α ⊕ β) K)
    (h0 : ∀ i, (H i).constantCoeff = 0)
    (hD : ∀ i j, (MvPowerSeries.pderiv j (H i)).constantCoeff =
      if j = Sum.inr i then 1 else 0) :
    ∀ i, H i - MvPowerSeries.X (Sum.inr i) ∈
      (IsLocalRing.maximalIdeal (MvPowerSeries (α ⊕ β) K)) ^ 2 := by
  classical
  intro i
  apply (powerSeries_firstJet_equal_iff_square _ _).mpr
  refine ⟨by simpa using h0 i, ?_⟩
  intro j
  rw [hD i j]
  simp [MvPowerSeries.pderiv_X, Pi.single_apply, eq_comm]

/-- Normalize actual target equations with a unit normal Jacobian. The
vanishing tangent derivatives are still explicit coordinate conditions. -/
theorem normalize_formal_normal_equations_firstOrder
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Nonempty β]
    (G : β → MvPowerSeries (α ⊕ β) K)
    (h0 : ∀ i, (G i).constantCoeff = 0)
    (hT : ∀ i j, (MvPowerSeries.pderiv (Sum.inl j) (G i)).constantCoeff = 0)
    (hJ : IsUnit (Matrix.det (fun i j =>
      (MvPowerSeries.pderiv (Sum.inr j) (G i)).constantCoeff))) :
    let J : Matrix β β K := fun i j =>
      (MvPowerSeries.pderiv (Sum.inr j) (G i)).constantCoeff
    let H := fun i => ∑ j, J⁻¹ i j • G j
    (∀ i, H i - MvPowerSeries.X (Sum.inr i) ∈
      (IsLocalRing.maximalIdeal (MvPowerSeries (α ⊕ β) K)) ^ 2) ∧
      Ideal.span (Set.range H) = Ideal.span (Set.range G) := by
  classical
  intro J H
  have h0H : ∀ i, (H i).constantCoeff = 0 := by
    intro i
    simp [H, map_sum, MvPowerSeries.constantCoeff_smul, h0]
  have hDH : ∀ i j, (MvPowerSeries.pderiv j (H i)).constantCoeff =
      if j = Sum.inr i then 1 else 0 := by
    intro i j
    cases j with
    | inl j => simp [H, map_sum, hT]
    | inr j =>
      have h := congrFun (congrFun (Matrix.nonsing_inv_mul J hJ) i) j
      change (∑ k, J⁻¹ i k * J k j) = (1 : Matrix β β K) i j at h
      simpa [H, J, map_sum, map_smul, Matrix.one_apply, eq_comm] using h
  refine ⟨normal_firstOrder_of_derivative_coordinates H h0H hDH, ?_⟩
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Ideal.sum_mem
    intro j hj
    simpa only [Algebra.smul_def] using
      (Ideal.span (Set.range G)).mul_mem_left
        (algebraMap K _ (J⁻¹ i j)) (Ideal.mem_span_range_self (x := j))
  · have hrecover : ∀ i, G i = ∑ j, J i j • H j := by
      intro i
      symm
      simp only [H, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul]
      have hh : ∀ k, (∑ j, J i j * J⁻¹ j k) = if i = k then 1 else 0 := by
        intro k
        have h := congrFun (congrFun (Matrix.mul_nonsing_inv J hJ) i) k
        change (∑ j, J i j * J⁻¹ j k) = (1 : Matrix β β K) i k at h
        simpa [Matrix.one_apply] using h
      simp [hh]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [hrecover i]
    apply Ideal.sum_mem
    intro j hj
    simpa only [Algebra.smul_def] using
      (Ideal.span (Set.range H)).mul_mem_left
        (algebraMap K _ (J i j)) (Ideal.mem_span_range_self (x := j))

end LinearStudy
