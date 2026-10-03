module

public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.Tactic.NormNum

/-! # The numerical examples and the warning about Bézout identities in Section 4.3 -/

@[expose] public section

namespace Section43.Examples

set_option autoImplicit false

theorem two_not_divides_one_int : ¬ (2 : ℤ) ∣ 1 := by norm_num

theorem two_divides_one_rat : (2 : ℚ) ∣ 1 := ⟨1 / 2, by norm_num⟩

theorem factorization_sixty : (60 : ℤ) = 2 ^ 2 * 3 * 5 := by norm_num

theorem gcd_seventyTwo_oneTwenty : Nat.gcd 72 120 = 24 := by norm_num

/-- Exercise: `(2 + i)i = -1 + 2i`. -/
theorem gaussian_associated :
    Associated (⟨2, 1⟩ : Zsqrtd (-1)) (⟨-1, 2⟩ : Zsqrtd (-1)) := by
  let u : (Zsqrtd (-1))ˣ :=
    ⟨⟨0, 1⟩, ⟨0, -1⟩, by ext <;> norm_num [Zsqrtd.re_mul, Zsqrtd.im_mul],
      by ext <;> norm_num [Zsqrtd.re_mul, Zsqrtd.im_mul]⟩
  refine ⟨u, ?_⟩
  ext <;> norm_num [u, Zsqrtd.re_mul, Zsqrtd.im_mul]

open Polynomial

theorem X_not_dvd_two : ¬ (X : ℤ[X]) ∣ C 2 := by
  rintro ⟨q, hq⟩
  have h := congrArg (eval 0) hq
  norm_num at h

/-- The section's warning: common divisors of `2` and `X` in `ℤ[X]` are units. -/
theorem two_X_relatively_prime : IsRelPrime (C 2 : ℤ[X]) X := by
  intro d hd2 hdX
  rcases (irreducible_X.dvd_iff.mp hdX) with hu | hassoc
  · exact hu
  · exact (X_not_dvd_two (hassoc.dvd.trans hd2)).elim

/-- The same pair admits no Bézout identity. -/
theorem two_X_no_bezout :
    ¬ ∃ u v : ℤ[X], (C 2 : ℤ[X]) * u + X * v = 1 := by
  rintro ⟨u, v, huv⟩
  have h := congrArg (eval 0) huv
  simp only [eval_add, eval_mul, eval_C, eval_X, zero_mul, add_zero, eval_one] at h
  omega

theorem two_X_not_isCoprime : ¬ IsCoprime (C 2 : ℤ[X]) X := by
  rintro ⟨u, v, huv⟩
  apply two_X_no_bezout
  exact ⟨u, v, by simpa only [mul_comm] using huv⟩

end Section43.Examples
