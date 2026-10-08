module
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Algebraic.Integral
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy

theorem transcendental_scaled_power
    {E F : Type*} [Field E] [Field F] [Algebra E F]
    (t : F) (ht : Transcendental E t) (u : E) (hu : u ≠ 0)
    (q : ℕ) (hq : 0 < q) :
    Transcendental E (algebraMap E F u * t ^ q) := by
  intro h
  have hmul := (isAlgebraic_algebraMap (R := E) (A := F) u⁻¹).mul h
  have he : algebraMap E F u⁻¹ * (algebraMap E F u * t ^ q) = t ^ q := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hu, map_one, one_mul]
  rw [he] at hmul
  exact ht (hmul.of_pow hq)

end LinearStudy
