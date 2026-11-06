module
public import Linear.PowerSeriesCoefficients
public import Linear.NilpotentEvaluation
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.RingTheory.MvPowerSeries.Derivative

/-!
# Algebraic uniqueness for evaluation at nilpotent variables

Partition the terms outside a finite coefficient box into multiples of
variable powers. Thus ring maps with nilpotent variable images are determined
by constants and variables, without assuming continuity of either map.
This supplies the canonical-map comparison needed for the diagonal method.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace LinearStudy
variable {R S : Type*} [CommRing R] [CommRing S]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem powerSeries_boxZero_expansion (H : MvPowerSeries ι R) (b : ι → ℕ)
    (hH : ∀ m : ι →₀ ℕ, (∀ i, m i < b i) → H.coeff m = 0) :
    ∃ a : ι → MvPowerSeries ι R, H = ∑ i, a i * MvPowerSeries.X i ^ b i := by
  classical
  have hex : ∀ m : ι →₀ ℕ, (¬ ∀ i, m i < b i) → ∃ i, b i ≤ m i := by
    intro m hm
    simpa only [not_forall, not_lt] using hm
  let v : (ι →₀ ℕ) → ι := fun m =>
    if hm : ∀ i, m i < b i then Classical.arbitrary ι else Classical.choose (hex m hm)
  have hv : ∀ m : ι →₀ ℕ, (¬ ∀ i, m i < b i) → b (v m) ≤ m (v m) := by
    intro m hm
    simp only [v, dite_eq_right hm]
    exact Classical.choose_spec (hex m hm)
  let part : ι → MvPowerSeries ι R := fun i m => if v m = i then H.coeff m else 0
  have hp : ∀ i, (MvPowerSeries.X i : MvPowerSeries ι R) ^ b i ∣ part i := by
    intro i
    rw [MvPowerSeries.X_pow_dvd_iff]
    intro m hm
    change (if v m = i then H.coeff m else 0) = 0
    by_cases hb : ∀ j, m j < b j
    · simp [hH m hb]
    · have hvi : v m ≠ i := by
        intro hi
        have h := hv m hb
        rw [hi] at h
        exact (Nat.not_le_of_lt hm) h
      simp [hvi]
  choose a ha using hp
  refine ⟨a, ?_⟩
  have hsum : H = ∑ i, part i := by
    ext m
    rw [map_sum]
    change H.coeff m = ∑ i, if v m = i then H.coeff m else 0
    simp [eq_comm]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ha i, mul_comm]

theorem powerSeries_map_eq_trunc_of_nilpotent
    (g : MvPowerSeries ι R →+* S) (b : ι → ℕ)
    (hb : ∀ i, g (MvPowerSeries.X i) ^ b i = 0) (H : MvPowerSeries ι R) :
    g H = g ((MvPowerSeries.trunc' R (Finsupp.equivFunOnFinite.symm b) H :
      MvPolynomial ι R) : MvPowerSeries ι R) := by
  classical
  let bound : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm b
  let p := MvPowerSeries.trunc' R bound H
  have hz : ∀ m : ι →₀ ℕ, (∀ i, m i < b i) →
      (H - (p : MvPowerSeries ι R)).coeff m = 0 := by
    intro m hm
    have hle : m ≤ bound := by
      intro i
      change m i ≤ b i
      exact Nat.le_of_lt (hm i)
    simp [p, map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_trunc', hle]
  obtain ⟨a, ha⟩ := powerSeries_boxZero_expansion (H - (p : MvPowerSeries ι R)) b hz
  have hzero : g (H - (p : MvPowerSeries ι R)) = 0 := by
    rw [ha, map_sum]
    simp only [map_mul, map_pow, hb, mul_zero, Finset.sum_const_zero]
  exact sub_eq_zero.mp (by simpa only [map_sub] using hzero)

theorem powerSeries_map_pderiv_eq_trunc_of_nilpotent
    (g : MvPowerSeries ι R →+* S) (b : ι → ℕ)
    (hb : ∀ i, g (MvPowerSeries.X i) ^ b i = 0)
    (H : MvPowerSeries ι R) (i : ι) :
    g (MvPowerSeries.pderiv i H) =
      g ((MvPolynomial.pderiv i (MvPowerSeries.trunc' R
        (Finsupp.equivFunOnFinite.symm (fun j => b j + 1)) H) :
        MvPolynomial ι R) : MvPowerSeries ι R) := by
  classical
  let bound : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun j => b j + 1)
  let p := MvPowerSeries.trunc' R bound H
  have hz : ∀ m : ι →₀ ℕ, (∀ j, m j < b j) →
      (MvPowerSeries.pderiv i (H - (p : MvPowerSeries ι R))).coeff m = 0 := by
    intro m hm
    have hle : m + Finsupp.single i 1 ≤ bound := by
      intro j
      change m j + (Finsupp.single i 1) j ≤ b j + 1
      by_cases hij : i = j
      · subst j; simp only [Finsupp.single_eq_same]; have := hm i; omega
      · simp only [Finsupp.single_eq_of_ne (Ne.symm hij)]; have := hm j; omega
    rw [MvPowerSeries.coeff_pderiv, map_sub, MvPolynomial.coeff_coe]
    simp [p, MvPowerSeries.coeff_trunc', hle]
  obtain ⟨a, ha⟩ := powerSeries_boxZero_expansion
    (MvPowerSeries.pderiv i (H - (p : MvPowerSeries ι R))) b hz
  have hzero : g (MvPowerSeries.pderiv i (H - (p : MvPowerSeries ι R))) = 0 := by
    rw [ha, map_sum]
    simp only [map_mul, map_pow, hb, mul_zero, Finset.sum_const_zero]
  rw [map_sub, MvPowerSeries.pderiv_coe, map_sub, sub_eq_zero] at hzero
  exact hzero

theorem powerSeries_nilpotent_ringHom_ext
    (g₁ g₂ : MvPowerSeries ι R →+* S)
    (hC : ∀ r, g₁ (MvPowerSeries.C r) = g₂ (MvPowerSeries.C r))
    (hX : ∀ i, g₁ (MvPowerSeries.X i) = g₂ (MvPowerSeries.X i))
    (hnil : ∀ i, IsNilpotent (g₁ (MvPowerSeries.X i))) : g₁ = g₂ := by
  classical
  choose b hb using hnil
  let bound : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm b
  have hpoly : ∀ p : MvPolynomial ι R, g₁ (p : MvPowerSeries ι R) = g₂ p := by
    have h := MvPolynomial.ringHom_ext
      (f := g₁.comp MvPolynomial.coeToMvPowerSeries.ringHom)
      (g := g₂.comp MvPolynomial.coeToMvPowerSeries.ringHom)
      (by intro r; simpa using hC r) (by intro i; simpa using hX i)
    exact fun p => RingHom.congr_fun h p
  apply RingHom.ext
  intro H
  let p := MvPowerSeries.trunc' R bound H
  have hz : ∀ m : ι →₀ ℕ, (∀ i, m i < b i) →
      (H - (p : MvPowerSeries ι R)).coeff m = 0 := by
    intro m hm
    have hle : m ≤ bound := by
      intro i
      change m i ≤ b i
      exact Nat.le_of_lt (hm i)
    simp [p, map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_trunc', hle]
  obtain ⟨a, ha⟩ := powerSeries_boxZero_expansion (H - (p : MvPowerSeries ι R)) b hz
  have hzero₁ : g₁ (H - (p : MvPowerSeries ι R)) = 0 := by
    rw [ha, map_sum]
    simp only [map_mul, map_pow, hb, mul_zero, Finset.sum_const_zero]
  have hzero₂ : g₂ (H - (p : MvPowerSeries ι R)) = 0 := by
    rw [ha, map_sum]
    simp only [map_mul, map_pow, ← hX, hb, mul_zero, Finset.sum_const_zero]
  rw [map_sub, sub_eq_zero] at hzero₁ hzero₂
  exact hzero₁.trans ((hpoly p).trans hzero₂.symm)

end LinearStudy
