module

public import Linear.DeterminantAnnihilator
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# Coefficient matrices for arbitrary multivariable power-series equations

Every zero-constant-coefficient series is a finite sum of variables times
series. Construct the summands by assigning each nonconstant monomial to
one variable occurring in it, then use mathlib's actual divisibility test.
The resulting equation matrix gives the determinant annihilator. Its
nonvanishing and comparison with the derivative Jacobian are still open.
-/

@[expose] public section
noncomputable section
namespace LinearStudy

variable {R : Type*} [CommRing R] {ι : Type*}
  [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A constructive coefficient partition proves variable-ideal membership;
no assumption about membership in that ideal is supplied. -/
theorem powerSeries_zeroConstant_variable_expansion (H : MvPowerSeries ι R)
    (hH : H.constantCoeff = 0) :
    ∃ a : ι → MvPowerSeries ι R, H = ∑ i, a i * MvPowerSeries.X i := by
  classical
  have hex : ∀ n : ι →₀ ℕ, n ≠ 0 → ∃ i, n i ≠ 0 := by
    intro n hn
    by_contra h
    push Not at h
    apply hn
    ext i
    exact h i
  let v : (ι →₀ ℕ) → ι := fun n =>
    if hn : n = 0 then Classical.arbitrary ι else Classical.choose (hex n hn)
  have hv : ∀ n : ι →₀ ℕ, n ≠ 0 → n (v n) ≠ 0 := by
    intro n hn
    simp only [v, dite_eq_right hn]
    exact Classical.choose_spec (hex n hn)
  let part : ι → MvPowerSeries ι R := fun i n => if v n = i then H.coeff n else 0
  have hp : ∀ i, (MvPowerSeries.X i : MvPowerSeries ι R) ∣ part i := by
    intro i
    rw [← pow_one (MvPowerSeries.X i), MvPowerSeries.X_pow_dvd_iff]
    intro n hn
    change (if v n = i then H.coeff n else 0) = 0
    by_cases hn0 : n = 0
    · subst n
      simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hH]
    · have hni : n i = 0 := Nat.lt_one_iff.mp hn
      have hvi : v n ≠ i := by
        intro h
        exact hv n hn0 (by rw [h, hni])
      simp [hvi]
  choose a ha using hp
  refine ⟨a, ?_⟩
  have hsum : H = ∑ i, part i := by
    ext n
    rw [map_sum]
    change H.coeff n = ∑ i, if v n = i then H.coeff n else 0
    simp [eq_comm]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ha i, mul_comm]

/-- Obtain a square coefficient matrix H = M X for arbitrary equations
with zero constant terms, in any finite nonempty number of variables. -/
theorem powerSeries_equation_coefficient_matrix
    (H : ι → MvPowerSeries ι R) (hH : ∀ i, (H i).constantCoeff = 0) :
    ∃ M : Matrix ι ι (MvPowerSeries ι R), M.mulVec MvPowerSeries.X = H := by
  choose M hM using fun i => powerSeries_zeroConstant_variable_expansion (H i) (hH i)
  refine ⟨M, ?_⟩
  funext i
  exact (hM i).symm

/-- The augmentation kernel really is the ideal of the variables, proved
for power series rather than borrowed from polynomial rings. -/
theorem powerSeries_constantCoeff_kernel :
    RingHom.ker (MvPowerSeries.constantCoeff (σ := ι) (R := R)) =
      Ideal.span (Set.range (MvPowerSeries.X (σ := ι) (R := R))) := by
  apply le_antisymm
  · intro H hH
    obtain ⟨a, ha⟩ := powerSeries_zeroConstant_variable_expansion H hH
    rw [ha]
    apply Submodule.sum_mem
    intro i hi
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries ι R) = 0
    simp

/-- The actual quotient has a coefficient-determinant annihilator of its
coordinate ideal. This assertion deliberately omits nonvanishing and the
Jacobian identification; neither follows from the adjugate identity alone. -/
theorem powerSeries_coefficientDeterminant_annihilator
    (H : ι → MvPowerSeries ι R) (hH : ∀ i, (H i).constantCoeff = 0) :
    let J := Ideal.span (Set.range H)
    ∃ M : Matrix ι ι (MvPowerSeries ι R),
      M.mulVec MvPowerSeries.X = H ∧
      Annihilates
        (Ideal.span (Set.range (fun i => Ideal.Quotient.mk J (MvPowerSeries.X i))))
        (Ideal.Quotient.mk J M.det) := by
  obtain ⟨M, hM⟩ := powerSeries_equation_coefficient_matrix H hH
  exact ⟨M, hM, coefficientDeterminant_annihilates_quotient H MvPowerSeries.X M hM⟩

/-- Over a field, the coordinate ideal in the actual quotient is maximal.
No finite-dimensionality or complete-intersection assumption is needed. -/
theorem powerSeries_quotient_coordinateIdeal_isMaximal {K : Type*} [Field K]
    (H : ι → MvPowerSeries ι K) (hH : ∀ i, (H i).constantCoeff = 0) :
    let J := Ideal.span (Set.range H)
    (Ideal.span (Set.range (fun i => Ideal.Quotient.mk J (MvPowerSeries.X i)))).IsMaximal := by
  let J := Ideal.span (Set.range H)
  let f := MvPowerSeries.constantCoeff (σ := ι) (R := K)
  have hf : Function.Surjective f := fun k => ⟨MvPowerSeries.C k, by simp [f]⟩
  let hmax := RingHom.ker_isMaximal_of_surjective f hf
  have hJ : J ≤ RingHom.ker f := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hH i
  have hm := Ideal.IsMaximal.map_of_surjective_of_ker_le
    (f := Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    (m := RingHom.ker f) (by simpa using hJ)
  have hk : RingHom.ker f = Ideal.span (Set.range (MvPowerSeries.X (σ := ι) (R := K))) :=
    powerSeries_constantCoeff_kernel
  rw [hk, Ideal.map_span, ← Set.range_comp] at hm
  exact hm

/-- The determinant is in the annihilator of a proved maximal ideal.
Nonzero socle generation and the Jacobian comparison are not asserted. -/
theorem powerSeries_coefficientDeterminant_maximal_annihilator
    {K : Type*} [Field K]
    (H : ι → MvPowerSeries ι K) (hH : ∀ i, (H i).constantCoeff = 0) :
    let J := Ideal.span (Set.range H)
    let m := Ideal.span (Set.range (fun i => Ideal.Quotient.mk J (MvPowerSeries.X i)))
    m.IsMaximal ∧ ∃ M : Matrix ι ι (MvPowerSeries ι K),
      M.mulVec MvPowerSeries.X = H ∧ Ideal.Quotient.mk J M.det ∈ m.annihilator := by
  obtain ⟨M, hM, hd⟩ := powerSeries_coefficientDeterminant_annihilator H hH
  exact ⟨powerSeries_quotient_coordinateIdeal_isMaximal H hH, M, hM,
    (annihilates_iff_mem_annihilator _ _).mp hd⟩

end LinearStudy
