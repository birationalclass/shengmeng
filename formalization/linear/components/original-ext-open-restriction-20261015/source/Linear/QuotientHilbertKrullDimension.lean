module
public import Linear.NoetherNormalizationKrull
public import Linear.QuotientNormalizationFilteredUpper
public import Linear.QuotientNormalizationFilteredLower
public import Linear.PolynomialGrowthDegreeComparison
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace LinearStudy
open Filter Polynomial
open scoped Topology

theorem homogeneousQuotientFiltration_finrank_pos
    {k σ : Type*} [Field k] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) [Nontrivial (MvPolynomial σ k ⧸ I)] (N : ℕ) :
    0 < Module.finrank k (homogeneousQuotientFiltration I N) := by
  letI := homogeneousQuotientFiltration_finite I N
  let a : homogeneousQuotientFiltration I N :=
    ⟨1, (homogeneousQuotientFiltration_mem_iff I N _).mpr ⟨1, by simp, map_one _⟩⟩
  exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨a, fun h =>
    one_ne_zero (congrArg Subtype.val h)⟩

/-- ACTUAL Noether normalization and the two constructed filtration bounds
identify an eventual ORIGINAL coordinate growth polynomial's degree with
the actual number of normalizing variables. -/
theorem quotient_normalization_hilbert_degree
    {k σ : Type*} [Field k] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) [Nontrivial (MvPolynomial σ k ⧸ I)]
    (s : ℕ) (g : MvPolynomial (Fin s) k →ₐ[k] (MvPolynomial σ k ⧸ I))
    (hinj : Function.Injective g) (hfin : g.Finite)
    (H : Polynomial ℚ) (hH : H ≠ 0)
    (hHilbert : ∃ K : ℕ, ∀ N > K,
      H.eval (N : ℚ) = (Module.finrank k (homogeneousQuotientFiltration I N) : ℚ)) :
    H.natDegree = s := by
  obtain ⟨K, hK⟩ := hHilbert
  have hHevent : ∀ᶠ N : ℕ in atTop,
      H.eval (N : ℚ) = (Module.finrank k (homogeneousQuotientFiltration I N) : ℚ) :=
    eventually_atTop.mpr ⟨K + 1, fun N hN => hK N (by omega)⟩
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < H.eval (N : ℚ) := by
    filter_upwards [hHevent] with N hN
    rw [hN]
    exact_mod_cast homogeneousQuotientFiltration_finrank_pos I N
  apply le_antisymm
  · obtain ⟨m, c, B, hc, hupper⟩ := quotient_normalization_filtration_upper I g hfin
    let Q : Polynomial ℚ := C (m : ℚ) * (C (c : ℚ) * X + C ((B + 1 : ℕ) : ℚ)) ^ s
    have hle : ∀ᶠ N : ℕ in atTop, H.eval (N : ℚ) ≤ Q.eval (N : ℚ) := by
      filter_upwards [hHevent] with N hN
      rw [hN]
      simp only [Q, eval_mul, eval_pow, eval_add, eval_C, eval_X]
      have hbound := hupper N
      simp only [Nat.card_fin] at hbound
      exact_mod_cast hbound
    have hdeg := polynomial_natDegree_le_of_eventually_le H Q hH hpos hle
    apply hdeg.trans
    calc
      Q.natDegree ≤ (C (m : ℚ)).natDegree +
          ((C (c : ℚ) * X + C ((B + 1 : ℕ) : ℚ)) ^ s).natDegree := natDegree_mul_le
      _ = s := by
        rw [natDegree_C, natDegree_pow,
          natDegree_linear (by exact_mod_cast hc.ne')]
        simp
  · by_cases hs : s = 0
    · simp [hs]
    obtain ⟨c, hc, hlower⟩ := quotient_normalization_filtration_lower I g hinj
    let a := c * s
    have ha : 0 < a := Nat.mul_pos hc (Nat.pos_of_ne_zero hs)
    let P : Polynomial ℚ := (X + 1) ^ s
    let Q : Polynomial ℚ := H.comp (C (a : ℚ) * X)
    have hP : P ≠ 0 := by
      apply pow_ne_zero s
      intro hz
      have he := congrArg (fun p : Polynomial ℚ => p.coeff 1) hz
      simp [Polynomial.coeff_one] at he
    have hPpos : ∀ᶠ N : ℕ in atTop, 0 < P.eval (N : ℚ) := by
      apply Filter.Eventually.of_forall
      intro N
      simp only [P, eval_pow, eval_add, eval_X, eval_one]
      positivity
    have hle : ∀ᶠ N : ℕ in atTop, P.eval (N : ℚ) ≤ Q.eval (N : ℚ) := by
      apply eventually_atTop.mpr
      refine ⟨K + 1, fun N hN => ?_⟩
      have hsmall : N ≤ a * N := by nlinarith
      have hlarge : a * N > K := by omega
      simp only [P, Q, eval_pow, eval_add, eval_X, eval_one,
        eval_comp, eval_mul, eval_C]
      rw [← Nat.cast_mul, hK (a * N) hlarge]
      have hbound : (N + 1) ^ s ≤
          Module.finrank k (homogeneousQuotientFiltration I (c * (s * N))) := by
        convert hlower N using 1
        · exact congrArg (fun j : ℕ => (N + 1) ^ j) (Nat.card_fin s).symm
        · exact congrArg (fun j : ℕ => Module.finrank k
            (homogeneousQuotientFiltration I (c * (j * N)))) (Nat.card_fin s).symm
      rw [show a * N = c * (s * N) by dsimp [a]; ring]
      exact_mod_cast hbound
    have hdeg := polynomial_natDegree_le_of_eventually_le P Q hP hPpos hle
    have hlin : (C (a : ℚ) * X).natDegree = 1 := by
      exact natDegree_C_mul_X _ (by exact_mod_cast ha.ne')
    have hPdeg : P.natDegree = s := by
      change ((X + C (1 : ℚ)) ^ s).natDegree = s
      rw [natDegree_pow, natDegree_X_add_C]
      simp
    simpa only [Q, natDegree_comp, hlin, mul_one, hPdeg] using hdeg

/-- The ORIGINAL coordinate quotient's Krull dimension is the degree of
its actual eventual cumulative Hilbert polynomial. All normalization and
growth comparisons are proved, not encoded as conclusion inputs. -/
theorem quotient_cumulative_hilbert_degree_eq_ringKrullDim
    {k σ : Type*} [Field k] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) [Nontrivial (MvPolynomial σ k ⧸ I)]
    (H : Polynomial ℚ) (hH : H ≠ 0)
    (hHilbert : ∃ K : ℕ, ∀ N > K,
      H.eval (N : ℚ) = (Module.finrank k (homogeneousQuotientFiltration I N) : ℚ)) :
    ringKrullDim (MvPolynomial σ k ⧸ I) = (H.natDegree : WithBot ℕ∞) := by
  obtain ⟨s, g, hinj, hfin, hdim⟩ := exists_finite_normalization_krull_dimension
    k (MvPolynomial σ k ⧸ I)
  have hdeg := quotient_normalization_hilbert_degree I s g hinj hfin H hH hHilbert
  simpa only [hdeg] using hdim

end LinearStudy
