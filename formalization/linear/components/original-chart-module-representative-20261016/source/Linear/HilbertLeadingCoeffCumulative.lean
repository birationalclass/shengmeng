module
public import Linear.HomogeneousCumulativeHilbert
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace LinearStudy
open Polynomial

/-- Exact highest possible coefficient of the Hilbert polynomial numerator expression. -/
theorem hilbertPoly_coeff_top (p : Polynomial ℚ) (r : ℕ) :
    (Polynomial.hilbertPoly p (r+1)).coeff r = p.eval 1 * (r.factorial : ℚ)⁻¹ := by
  rw [Polynomial.hilbertPoly_succ]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul, smul_eq_mul,
    Polynomial.coeff_preHilbertPoly_self, ← Finset.sum_mul]
  congr 1
  simp only [Polynomial.eval_eq_sum, one_pow, mul_one, Polynomial.sum_def]

/-- When the numerator does not vanish at 1, its factorial-normalized leading
coefficient is precisely its value at 1. -/
theorem hilbertPoly_leadingCoeff_of_eval_one_ne_zero
    (p : Polynomial ℚ) (hp : p.eval 1 ≠ 0) (r : ℕ) :
    (Polynomial.hilbertPoly p (r+1)).leadingCoeff =
      p.eval 1 * (r.factorial : ℚ)⁻¹ := by
  have hp0 : p ≠ 0 := by
    intro h
    simp [h] at hp
  have hr : p.rootMultiplicity 1 = 0 := by
    exact Polynomial.rootMultiplicity_eq_zero (by simpa [Polynomial.IsRoot] using hp)
  have hd : (Polynomial.hilbertPoly p (r+1)).natDegree = r := by
    rw [Polynomial.natDegree_hilbertPoly_of_ne_zero_of_rootMultiplicity_lt hp0
      (by rw [hr]; omega), hr]
    omega
  rw [Polynomial.leadingCoeff, hd, hilbertPoly_coeff_top]

/-- One cumulative sum preserves the factorial-normalized Hilbert leading coefficient.
No geometric degree or generic rank equality is an assumption. -/
theorem hilbertPoly_cumulative_normalized_leadingCoeff
    (p : Polynomial ℚ) (D : ℕ) (hP : Polynomial.hilbertPoly p D ≠ 0) :
    (((Polynomial.hilbertPoly p (D+1)).natDegree).factorial : ℚ) *
      (Polynomial.hilbertPoly p (D+1)).leadingCoeff =
    (((Polynomial.hilbertPoly p D).natDegree).factorial : ℚ) *
      (Polynomial.hilbertPoly p D).leadingCoeff := by
  have hp : p ≠ 0 := by
    intro hp
    subst p
    exact hP (Polynomial.hilbertPoly_zero_left D)
  have ht : p.rootMultiplicity 1 < D := by
    by_contra h
    exact hP (Polynomial.hilbertPoly_eq_zero_of_le_rootMultiplicity_one (not_lt.mp h))
  obtain ⟨q,hq,hqn⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 1
  let a : Polynomial ℚ := q * (-1) ^ p.rootMultiplicity 1
  have ha : a.eval 1 ≠ 0 := by
    have hq1 : q.eval 1 ≠ 0 := by
      simpa [Polynomial.IsRoot] using (not_iff_not.mpr Polynomial.dvd_iff_isRoot).mp hqn
    simp [a, hq1]
  have heq : p = a * (1 - X) ^ p.rootMultiplicity 1 := by
    simp only [a, mul_assoc, ← mul_pow, neg_mul, one_mul, neg_sub]
    exact hq.trans (mul_comm _ _)
  let r := D - p.rootMultiplicity 1 - 1
  have hD : D = (r+1) + p.rootMultiplicity 1 := by dsimp [r]; omega
  have hD1 : D+1 = (r+2) + p.rootMultiplicity 1 := by omega
  have eP : Polynomial.hilbertPoly p D = Polynomial.hilbertPoly a (r+1) := by
    rw [heq, hD, Polynomial.hilbertPoly_mul_one_sub_pow_add]
  have eC : Polynomial.hilbertPoly p (D+1) = Polynomial.hilbertPoly a (r+2) := by
    rw [heq, hD1, Polynomial.hilbertPoly_mul_one_sub_pow_add]
  have hdP : (Polynomial.hilbertPoly p D).natDegree = r := by
    exact Polynomial.natDegree_hilbertPoly_of_ne_zero hP
  have hdC : (Polynomial.hilbertPoly p (D+1)).natDegree = r+1 := by
    rw [hilbertPoly_natDegree_succ p D hP, hdP]
  rw [hdC, hdP, eP, eC,
    hilbertPoly_leadingCoeff_of_eval_one_ne_zero a ha r,
    show r+2 = (r+1)+1 by omega,
    hilbertPoly_leadingCoeff_of_eval_one_ne_zero a ha (r+1)]
  have hrf : (r.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hrf1 : ((r+1).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (r+1)
  field_simp

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual quotient filtration has the same factorial-normalized leading
coefficient as its actual homogeneous-piece Hilbert polynomial. -/
theorem homogeneousQuotientCumulativeHilbertPolynomial_normalized_leadingCoeff
    {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (P : Polynomial ℚ) (hP : P ≠ 0)
    (hN : ∃ N : ℕ, ∀ n > N,
      P.eval (n : ℚ) = (homogeneousQuotientHilbert I n : ℚ)) :
    ∃ C : Polynomial ℚ, C ≠ 0 ∧ C.natDegree = P.natDegree+1 ∧
      (C.natDegree.factorial : ℚ) * C.leadingCoeff =
        (P.natDegree.factorial : ℚ) * P.leadingCoeff ∧
      ∃ N : ℕ, ∀ n > N,
        C.eval (n : ℚ) = (Module.finrank K (homogeneousQuotientFiltration I n) : ℚ) := by
  obtain ⟨p,hp⟩ := homogeneousQuotientHilbertSeries_rational I hI
  obtain ⟨C,hC,_⟩ := homogeneousQuotientCumulativeHilbertPolynomial_existsUnique I hI
  let φ : ℤ →+* ℚ := Int.castRingHom ℚ
  let H := PowerSeries.map φ (gradedHilbertSeries (homogeneousQuotientPiece I))
  let G := PowerSeries.map φ (gradedHilbertSeries (homogeneousQuotientFiltration I))
  let pQ := Polynomial.map φ p
  have hH : (1 - PowerSeries.X) ^ Nat.card σ * H = (pQ : PowerSeries ℚ) := by
    simpa [H,pQ] using congrArg (PowerSeries.map φ) hp
  have hrec : (1-PowerSeries.X)*G=H := by
    simpa [G,H] using congrArg (PowerSeries.map φ)
      (homogeneousQuotientFiltration_series_recurrence I hI)
  have hG : (1-PowerSeries.X)^(Nat.card σ+1)*G=(pQ : PowerSeries ℚ) := by
    calc
      _ = (1-PowerSeries.X)^Nat.card σ*((1-PowerSeries.X)*G) := by ring
      _ = (1-PowerSeries.X)^Nat.card σ*H := by rw [hrec]
      _ = (pQ : PowerSeries ℚ) := hH
  have hcoeff (n : ℕ) : PowerSeries.coeff n H=(homogeneousQuotientHilbert I n : ℚ) := by
    simp [H,φ,gradedHilbertSeries,PowerSeries.coeff_map,homogeneousQuotientHilbert]
  have gcoeff (n : ℕ) : PowerSeries.coeff n G=
      (Module.finrank K (homogeneousQuotientFiltration I n) : ℚ) := by
    simp [G,φ,gradedHilbertSeries,PowerSeries.coeff_map]
  have heP : P=Polynomial.hilbertPoly pQ (Nat.card σ) := by
    apply hilbertPolynomial_eq_of_rational_series H pQ (Nat.card σ) hH
    obtain ⟨N,hN⟩ := hN
    exact ⟨N,fun n hn => by rw [hcoeff n,hN n hn]⟩
  have heC : C=Polynomial.hilbertPoly pQ (Nat.card σ+1) := by
    apply hilbertPolynomial_eq_of_rational_series G pQ (Nat.card σ+1) hG
    obtain ⟨N,hC⟩ := hC
    exact ⟨N,fun n hn => by rw [gcoeff n,hC n hn]⟩
  have hd : C.natDegree=P.natDegree+1 := by
    rw [heC,heP]
    exact hilbertPoly_natDegree_succ pQ (Nat.card σ) (heP ▸ hP)
  have hC0 : C ≠ 0 := by
    intro h
    simp only [h,Polynomial.natDegree_zero] at hd
    omega
  refine ⟨C,hC0,hd,?_,hC⟩
  rw [heC,heP]
  exact hilbertPoly_cumulative_normalized_leadingCoeff pQ (Nat.card σ) (heP ▸ hP)

end LinearStudy
