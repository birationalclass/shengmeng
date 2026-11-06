module
public import Linear.OriginalDegreeVeroneseCoefficientLocalization
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
universe u v w
variable {K : Type u} {S : Type v} {M : Type w}
variable [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (D : ℤ → Submodule K M)
variable (hD : ∀ (n : ℕ) (d : ℤ) (c : S), c ∈ B n →
  ∀ x : M, x ∈ D d → c • x ∈ D ((n : ℤ) + d))

include hD in
/-- Raise the denominator of a homogeneous fraction to the qth power.
The new numerator lies in the original degree q*(n+k). -/
theorem originalDegreeVeronesePromotedNumerator_mem
    (q : ℕ) (hq : 0 < q) (n : ℕ) (k : ℤ)
    (b : S) (hb : b ∈ B n) (x : M) (hx : x ∈ D ((n : ℤ) + (q : ℤ)*k)) :
    b^(q-1) • x ∈ D ((q : ℤ) * ((n : ℤ) + k)) := by
  have hpow : b^(q-1) ∈ B ((q-1)*n) := by
    simpa only [smul_eq_mul] using SetLike.pow_mem_graded (q-1) hb
  have h := hD ((q-1)*n) ((n : ℤ) + (q : ℤ)*k) (b^(q-1)) hpow x hx
  have he : (q-1)*n+n = q*n := calc
    (q-1)*n+n = (q-1)*n+1*n := by rw [one_mul]
    _ = (q-1+1)*n := (Nat.add_mul (q-1) 1 n).symm
    _ = q*n := congrArg (· * n) (Nat.sub_add_cancel hq)
  rw [← add_assoc, ← Nat.cast_add, he, Nat.cast_mul, ← mul_add] at h
  exact h

/-- The promoted fraction has the same value in every localized module
where the original denominator is permitted. -/
theorem originalDegreeVeronesePromotedFraction_eq
    (q : ℕ) (hq : 0 < q) (T : Submonoid S) (b : T) (x : M) :
    LocalizedModule.mk ((b : S)^(q-1) • x) (b^q) = LocalizedModule.mk x b := by
  have hden : b^(q-1)*b = b^q := by
    rw [← pow_succ, Nat.sub_add_cancel hq]
  rw [← hden]
  exact LocalizedModule.mk_cancel_common_left (b^(q-1)) b x

end LinearStudy
#check LinearStudy.originalDegreeVeronesePromotedNumerator_mem
#print axioms LinearStudy.originalDegreeVeronesePromotedNumerator_mem
#check LinearStudy.originalDegreeVeronesePromotedFraction_eq
#print axioms LinearStudy.originalDegreeVeronesePromotedFraction_eq

