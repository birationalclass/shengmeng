import PowerFactors
noncomputable section
namespace JordanSize
variable {A : Type*} [Ring A] [Algebra ℚ A]
lemma exp_integer (D : A) (hD : IsNilpotent D) (U : Aˣ)
    (hU : (U : A) = IsNilpotent.exp D) (m : ℤ) :
    ((U^m : Aˣ) : A) = IsNilpotent.exp ((m : ℚ) • D) := by
  cases m with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val,
      hU, Int.cast_natCast, exp_nat D hD]
  | negSucc n =>
    rw [zpow_negSucc]
    apply (U.isUnit.pow (n+1)).mul_left_cancel
    have he : (U : A)^(n+1) * IsNilpotent.exp ((Int.negSucc n : ℚ) • D) = 1 := by
      rw [hU, ← exp_nat D hD]
      rw [← IsNilpotent.exp_add_of_commute
        (((Commute.refl D).smul_left ((n+1 : ℕ) : ℚ)).smul_right _)
        (hD.smul _) (hD.smul _), ← add_smul]
      simp
    calc (U : A)^(n+1) * (((U^(n+1))⁻¹ : Aˣ) : A) = 1 := by
           rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, mul_inv_cancel]
           rfl
         _ = (U : A)^(n+1) * IsNilpotent.exp ((Int.negSucc n : ℚ) • D) := he.symm
end JordanSize
#print axioms JordanSize.exp_integer
