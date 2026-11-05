module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# The reduction and annihilator step in Linear Lemma 3.1

These results concern actual commutative rings and algebra maps. They do not
assume or claim a complete-intersection/Jacobian theorem.
-/

@[expose] public section

namespace LinearStudy

variable {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]

/-- An element annihilates the ideal `N`. -/
def Annihilates (N : Ideal A) (x : A) : Prop :=
  ∀ n ∈ N, n * x = 0

/-- Multiplication by an annihilator element factors through the reduction map. -/
theorem multiplication_factors_through_reduction
    (q : A →ₐ[B] B) (hq : ∀ a, q a = 0 ↔ a ∈ nilradical A)
    {x : A} (hx : Annihilates (nilradical A) x) (a : A) :
    a * x = algebraMap B A (q a) * x := by
  have hn : a - algebraMap B A (q a) ∈ nilradical A := by
    apply (hq _).mp
    simp
  have h := hx _ hn
  simpa only [sub_mul, sub_eq_zero] using h

/-- The source ideal remains an ideal; scalar generation is possible because
its action factors through the reduced algebra. -/
theorem scalar_multiple_annihilates
    (N : Ideal A) {x : A} (hx : Annihilates N x) (b : B) :
    Annihilates N (b • x) := by
  intro n hn
  rw [Algebra.smul_def, ← mul_assoc, mul_comm n (algebraMap B A b), mul_assoc,
    hx n hn, mul_zero]

/-- Same reduced value means the same action on the annihilator. -/
theorem annihilator_action_eq
    (q : A →ₐ[B] B) (hq : ∀ a, q a = 0 ↔ a ∈ nilradical A)
    {x : A} (hx : Annihilates (nilradical A) x) {a a' : A}
    (h : q a = q a') : a * x = a' * x := by
  rw [multiplication_factors_through_reduction q hq hx a,
    multiplication_factors_through_reduction q hq hx a', h]

/-- The natural quotient image of an element is zero precisely when the element
belongs to the ideal being quotiented out. -/
theorem quotient_image_nonzero_iff (J : Ideal A) (delta : A) :
    Ideal.Quotient.mk J delta ≠ 0 ↔ delta ∉ J := by
  exact not_congr (Ideal.Quotient.eq_zero_iff_mem)

end LinearStudy
