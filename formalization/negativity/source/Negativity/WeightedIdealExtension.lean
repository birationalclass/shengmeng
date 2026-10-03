module

public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic

@[expose] public section
namespace Negativity
noncomputable section

variable {R F : Type*} [CommRing R] [Field F]

/-- Elements of a subring whose product with a specified weight power
stays in the subring. The weight itself need not belong to the subring. -/
def weightedSubringIdeal (V : Subring F) (t : F) (n : ℕ) : Ideal V where
  carrier := {r | (r : F) * t ^ n ∈ V}
  zero_mem' := by simp
  add_mem' {r s} hr hs := by
    change (r : F) * t ^ n ∈ V at hr
    change (s : F) * t ^ n ∈ V at hs
    change ((r + s : V) : F) * t ^ n ∈ V
    simpa only [Subring.coe_add, add_mul] using V.add_mem hr hs
  smul_mem' a r hr := by
    change (r : F) * t ^ n ∈ V at hr
    change ((a • r : V) : F) * t ^ n ∈ V
    simpa only [smul_eq_mul, Subring.coe_mul, mul_assoc] using
      V.mul_mem a.property hr

theorem weighted_subring_ideal_mul (V : Subring F) (t : F) (n : ℕ) :
    weightedSubringIdeal V t 1 * weightedSubringIdeal V t n ≤
      weightedSubringIdeal V t (n + 1) := by
  apply Ideal.mul_le.mpr
  intro r hr s hs
  change (r : F) * t ^ 1 ∈ V at hr
  change (s : F) * t ^ n ∈ V at hs
  change ((r * s : V) : F) * t ^ (n + 1) ∈ V
  have hh := V.mul_mem hr hs
  change ((r : F) * t ^ 1) * ((s : F) * t ^ n) ∈ V at hh
  convert hh using 1 <;> simp only [Subring.coe_mul, pow_succ] <;> ring

/-- Final theorem: if every element of an ideal multiplied by a weight
lies in a subring, every element of its n-th extended ideal power,
multiplied by the n-th weight power, also lies in that subring. This
includes all sums and subring scalar coefficients in ideal extension. -/
theorem weighted_ideal_extension_mem
    (I : Ideal R) (V : Subring F) (g : R →+* V) (t : F)
    (hI : ∀ r ∈ I, (g r : F) * t ∈ V)
    (n : ℕ) (r : V) (hr : r ∈ (I ^ n).map g) :
    (r : F) * t ^ n ∈ V := by
  have hbase : I.map g ≤ weightedSubringIdeal V t 1 := by
    apply Ideal.span_le.mpr
    rintro _ ⟨s, hs, rfl⟩
    change (g s : F) * t ^ 1 ∈ V
    simpa only [pow_one] using hI s hs
  have hall (n : ℕ) : (I.map g) ^ n ≤ weightedSubringIdeal V t n := by
    induction n with
    | zero =>
      intro x _
      change (x : F) * t ^ 0 ∈ V
      simpa only [pow_zero, mul_one] using x.property
    | succ n hn =>
      rw [pow_succ']
      exact (Ideal.mul_mono hbase hn).trans (weighted_subring_ideal_mul V t n)
  exact hall n (by simpa only [Ideal.map_pow] using hr)

end
end Negativity
