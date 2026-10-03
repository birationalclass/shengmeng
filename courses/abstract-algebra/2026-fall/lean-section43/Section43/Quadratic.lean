module

public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.IntervalCases

/-! # Section 4.3: quadratic norms and the failure of unique factorization -/

@[expose] public section

namespace Section43

set_option autoImplicit false

namespace Quadratic

/-- The course uses the absolute norm; mathlib's `Zsqrtd.norm` is signed. -/
def absNorm {d : ℤ} (z : Zsqrtd d) : ℕ := z.norm.natAbs

theorem absNorm_formula {d : ℤ} (z : Zsqrtd d) :
    absNorm z = (z.re ^ 2 - d * z.im ^ 2).natAbs := by
  simp only [absNorm, Zsqrtd.norm_def, pow_two, mul_assoc]

/-- Theorem 4.3.4(1). -/
theorem absNorm_mul {d : ℤ} (z w : Zsqrtd d) :
    absNorm (z * w) = absNorm z * absNorm w := by
  simp only [absNorm, Zsqrtd.norm_mul, Int.natAbs_mul]

/-- The squarefree hypotheses in the course imply the nonsquare hypothesis used by mathlib. -/
theorem squarefree_nonsquare {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1) :
    ∀ n : ℤ, d ≠ n * n := by
  intro n heq
  have hu : IsUnit n := hd n (heq ▸ dvd_rfl)
  rcases Int.isUnit_eq_one_or hu with h | h <;> subst n <;> norm_num at heq
  all_goals exact hd1 heq

/-- Theorem 4.3.4(2), with the original squarefree hypotheses. -/
theorem absNorm_eq_zero_iff {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    (z : Zsqrtd d) : absNorm z = 0 ↔ z = 0 := by
  rw [absNorm, Int.natAbs_eq_zero]
  exact Zsqrtd.norm_eq_zero (squarefree_nonsquare hd hd1) z

/-- Theorem 4.3.4(3); this holds even without the squarefree hypothesis. -/
theorem absNorm_eq_one_iff {d : ℤ} (z : Zsqrtd d) :
    absNorm z = 1 ↔ IsUnit z := Zsqrtd.norm_eq_one_iff

/-- Theorem 4.3.4(4). -/
theorem absNorm_dvd_of_dvd {d : ℤ} {z w : Zsqrtd d} (h : z ∣ w) :
    absNorm z ∣ absNorm w := by
  obtain ⟨v, rfl⟩ := h
  rw [absNorm_mul]
  exact dvd_mul_right _ _

end Quadratic

namespace MinusThree

abbrev D := Zsqrtd (-3)

def plus : D := ⟨1, 1⟩
def minus : D := ⟨1, -1⟩

theorem norm_nonneg (z : D) : 0 ≤ z.norm := Zsqrtd.norm_nonneg (by norm_num) z

/-- The example really is an integral domain, not merely a quadratic ring. -/
instance : NoZeroDivisors D where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    have hm : a.norm * b.norm = 0 := by rw [← Zsqrtd.norm_mul, h, Zsqrtd.norm_zero]
    exact (mul_eq_zero.mp hm).imp
      ((Zsqrtd.norm_eq_zero_iff (by norm_num) a).mp)
      ((Zsqrtd.norm_eq_zero_iff (by norm_num) b).mp)

instance : IsDomain D := NoZeroDivisors.to_isDomain D

theorem absNorm_ne_zero {a : D} (ha : a ≠ 0) : Quadratic.absNorm a ≠ 0 := by
  intro h
  have hn : a.norm = 0 := Int.natAbs_eq_zero.mp h
  exact ha ((Zsqrtd.norm_eq_zero_iff (by norm_num : (-3 : ℤ) < 0) a).mp hn)

/-- Norm descent gives factorization existence even though uniqueness fails. -/
theorem nonzero_accessible (a : D) (ha : a ≠ 0) : Acc DvdNotUnit a := by
  have hacc : ∀ n : ℕ, ∀ a : D, Quadratic.absNorm a = n → a ≠ 0 → Acc DvdNotUnit a := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a hna ha
      refine Acc.intro a ?_
      intro b hba
      obtain ⟨hb, c, hcu, heq⟩ := hba
      have hc : c ≠ 0 := by intro hc; simp [hc] at heq; exact ha heq
      have hbn := absNorm_ne_zero hb
      have hcn := absNorm_ne_zero hc
      have hc1 : Quadratic.absNorm c ≠ 1 :=
        fun h ↦ hcu ((Quadratic.absNorm_eq_one_iff c).mp h)
      have hlt : Quadratic.absNorm b < n := by
        rw [← hna, heq, Quadratic.absNorm_mul]
        have hc2 : 2 ≤ Quadratic.absNorm c := by omega
        have hb1 : 1 ≤ Quadratic.absNorm b := by omega
        nlinarith
      exact ih _ hlt b rfl hb
  exact hacc _ a rfl ha

instance : WfDvdMonoid D := by
  constructor
  intro a
  by_cases ha : a = 0
  · subst a
    exact Acc.intro 0 (fun b hb ↦ nonzero_accessible b hb.1)
  · exact nonzero_accessible a ha

theorem irreducible_factorization_exists (a : D) (ha : a ≠ 0) :
    ∃ f : Multiset D, (∀ p ∈ f, Irreducible p) ∧ Associated f.prod a :=
  WfDvdMonoid.exists_factors a ha

/-- There is no element of norm two in `ℤ[√(-3)]`. -/
theorem no_norm_two (z : D) : z.norm ≠ 2 := by
  intro h
  have him : z.im = 0 := by
    by_contra hi
    have hi2 : 1 ≤ z.im * z.im := by
      have hi' : z.im ≤ -1 ∨ 1 ≤ z.im := by omega
      rcases hi' with hneg | hpos <;> nlinarith
    have hr2 := mul_self_nonneg z.re
    simp only [Zsqrtd.norm_def] at h
    nlinarith
  simp only [Zsqrtd.norm_def, him, mul_zero, sub_zero] at h
  have hlo : -1 ≤ z.re := by nlinarith [sq_nonneg (z.re + 1)]
  have hhi : z.re ≤ 1 := by nlinarith [sq_nonneg (z.re - 1)]
  interval_cases z.re <;> norm_num at h

/-- Any element of norm four is irreducible, since norm two is impossible. -/
theorem irreducible_of_norm_four {z : D} (hz : z.norm = 4) : Irreducible z := by
  constructor
  · intro hu
    have h1 := (Zsqrtd.norm_eq_one_iff' (by norm_num : (-3 : ℤ) ≤ 0) z).mpr hu
    omega
  · intro a b hab
    have hm : a.norm * b.norm = 4 := by rw [← Zsqrtd.norm_mul, ← hab, hz]
    have ha := norm_nonneg a
    have hb := norm_nonneg b
    have ha0 : 1 ≤ a.norm := by nlinarith
    have hb0 : 1 ≤ b.norm := by nlinarith
    have ha4 : a.norm ≤ 4 := by nlinarith
    have hb4 : b.norm ≤ 4 := by nlinarith
    have hne := no_norm_two a
    have hunit : a.norm = 1 ∨ b.norm = 1 := by
      interval_cases a.norm <;> norm_num at hm ⊢ <;> omega
    exact hunit.imp
      ((Zsqrtd.norm_eq_one_iff' (by norm_num) a).mp)
      ((Zsqrtd.norm_eq_one_iff' (by norm_num) b).mp)

theorem two_irreducible : Irreducible (2 : D) :=
  irreducible_of_norm_four (by norm_num [Zsqrtd.norm_def])

theorem plus_irreducible : Irreducible plus :=
  irreducible_of_norm_four (by norm_num [plus, Zsqrtd.norm_def])

theorem minus_irreducible : Irreducible minus :=
  irreducible_of_norm_four (by norm_num [minus, Zsqrtd.norm_def])

theorem units_are_signs (u : Dˣ) : (u : D) = 1 ∨ (u : D) = -1 := by
  have hn := (Zsqrtd.norm_eq_one_iff' (by norm_num : (-3 : ℤ) ≤ 0) (u : D)).mpr u.isUnit
  have him : (u : D).im = 0 := by
    by_contra hi
    have hi' : (u : D).im ≤ -1 ∨ 1 ≤ (u : D).im := by omega
    have hi2 : 1 ≤ (u : D).im * (u : D).im := by
      rcases hi' with hneg | hpos <;> nlinarith
    simp only [Zsqrtd.norm_def] at hn
    nlinarith [mul_self_nonneg (u : D).re]
  have hr : (u : D).re = 1 ∨ (u : D).re = -1 := by
    simp only [Zsqrtd.norm_def, him, mul_zero, sub_zero] at hn
    have hm : ((u : D).re - 1) * ((u : D).re + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hm with hpos | hneg
    · left; linarith
    · right; linarith
  rcases hr with hpos | hneg
  · left
    apply Zsqrtd.ext
    · simpa using hpos
    · simpa using him
  · right
    apply Zsqrtd.ext
    · simpa using hneg
    · simpa using him

theorem plus_not_associated_minus : ¬ Associated plus minus := by
  rintro ⟨u, hu⟩
  rcases units_are_signs u with hpos | hneg
  · have him := congrArg Zsqrtd.im hu
    simp [hpos, plus, minus] at him
  · have hre := congrArg Zsqrtd.re hu
    simp [hneg, plus, minus] at hre

/-- The displayed equality from the course. -/
theorem two_factorizations : (2 : D) * 2 = plus * minus := by
  ext <;> norm_num [plus, minus, Zsqrtd.re_mul, Zsqrtd.im_mul]

theorem two_not_dvd_plus : ¬ (2 : D) ∣ plus := by
  rintro ⟨v, hv⟩
  have hre := congrArg Zsqrtd.re hv
  norm_num [plus, Zsqrtd.re_mul] at hre
  omega

theorem two_not_dvd_minus : ¬ (2 : D) ∣ minus := by
  rintro ⟨v, hv⟩
  have hre := congrArg Zsqrtd.re hv
  norm_num [minus, Zsqrtd.re_mul] at hre
  omega

theorem two_not_associated_plus : ¬ Associated (2 : D) plus :=
  fun h ↦ two_not_dvd_plus h.dvd

theorem two_not_associated_minus : ¬ Associated (2 : D) minus :=
  fun h ↦ two_not_dvd_minus h.dvd

/-- A certified counterexample to irreducible implying prime in arbitrary domains. -/
theorem two_not_prime : ¬ Prime (2 : D) := by
  intro hp
  have hd : (2 : D) ∣ plus * minus := ⟨2, two_factorizations.symm⟩
  exact (hp.dvd_or_dvd hd).elim two_not_dvd_plus two_not_dvd_minus

/-- The example ring cannot satisfy unique factorization. -/
theorem not_uniqueFactorizationMonoid : ¬ UniqueFactorizationMonoid D := by
  intro h
  exact two_not_prime (h.irreducible_iff_prime.mp two_irreducible)

end MinusThree

end Section43
