module
public import Linear.OriginalDegreeVeronesePrimeReflect
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u v w
variable {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (q : ℕ) [hq : Fact (0 < q)]
local notation "P" => originalDegreeVeronesePiece B q
local instance originalDegreeVeronesePrimeSameShiftGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out
local notation "V" => originalDegreeVeroneseAlgebra B q
local notation "F" => originalDegreeVeroneseProjHom B q

local notation "Q" => originalDegreeVeroneseRegradedPrimeCompl B q
local notation "T" => originalDegreeVeroneseAmbientPrimeCompl B

variable {M : Type w} [AddCommGroup M] [Module K M] [Module S M]
variable (D : ℤ → Submodule K M)
variable (hD : ∀ (n : ℕ) (d : ℤ) (c : S), c ∈ B n →
  ∀ a : M, a ∈ D d → c • a ∈ D ((n : ℤ) + d))
local notation "W" => originalDegreeVeroneseCoefficient B D hD q

private theorem cross_degree_comm (q d e : ℕ) (k : ℤ) :
    (↑(q*d) : ℤ) + (q : ℤ)*((e : ℤ)+k) =
    (↑(q*e) : ℤ) + (q : ℤ)*((d : ℤ)+k) := by
  simp only [Nat.cast_mul, mul_add]
  exact add_left_comm ((q : ℤ)*(d : ℤ)) ((q : ℤ)*(e : ℤ)) ((q : ℤ)*k)

theorem originalDegreeVeronesePrimeCrossDifference_mem
    (x : Proj B) (k : ℤ) {d e : ℕ} (a b : W) (s t : Q x)
    (hs : (s : V) ∈ P d) (ht : (t : V) ∈ P e)
    (ha : (a : M) ∈ D ((q : ℤ)*((d : ℤ)+k)))
    (hb : (b : M) ∈ D ((q : ℤ)*((e : ℤ)+k))) :
    ((t : V) : S) • (a : M) - ((s : V) : S) • (b : M) ∈
      D ((↑(q*e) : ℤ) + (q : ℤ)*((d : ℤ)+k)) := by
  have h₁ := hD (q*e) ((q : ℤ)*((d : ℤ)+k)) ((t : V) : S) ht (a : M) ha
  have h₂ := hD (q*d) ((q : ℤ)*((e : ℤ)+k)) ((s : V) : S) hs (b : M) hb
  have h₃ : ((s : V) : S) • (b : M) ∈
      D ((↑(q*e) : ℤ) + (q : ℤ)*((d : ℤ)+k)) :=
    (congrArg (fun i : ℤ => ((s : V) : S) • (b : M) ∈ D i)
      (cross_degree_comm q d e k)).mp h₂
  exact (D _).sub_mem h₁ h₃

variable [DirectSum.Decomposition D]

/-- The actual prime-localization comparison reflects equality on the same shift. -/
theorem originalDegreeVeronesePrimeLocalization_sameShift_eq_iff
    (x : Proj B) (k : ℤ) {d e : ℕ} (a b : W) (s t : Q x)
    (hs : (s : V) ∈ P d) (ht : (t : V) ∈ P e)
    (ha : (a : M) ∈ D ((q : ℤ)*((d : ℤ)+k)))
    (hb : (b : M) ∈ D ((q : ℤ)*((e : ℤ)+k))) :
    originalDegreeVeronesePrimeLocalization B q D hD x (LocalizedModule.mk a s) =
      originalDegreeVeronesePrimeLocalization B q D hD x (LocalizedModule.mk b t) ↔
    LocalizedModule.mk a s = LocalizedModule.mk b t := by
  constructor
  · intro h
    have h₁ := originalDegreeVeronesePrimeLocalization_mk B q D hD x a s
    have h₂ := originalDegreeVeronesePrimeLocalization_mk B q D hD x b t
    exact originalDegreeVeronesePrimeLocalization_reflect B q D hD x a b s t _
      (originalDegreeVeronesePrimeCrossDifference_mem B q D hD x k a b s t hs ht ha hb)
      (h₁.symm.trans (h.trans h₂))
  · exact congrArg (originalDegreeVeronesePrimeLocalization B q D hD x)

end LinearStudy
#check LinearStudy.originalDegreeVeronesePrimeCrossDifference_mem
#print axioms LinearStudy.originalDegreeVeronesePrimeCrossDifference_mem
#check LinearStudy.originalDegreeVeronesePrimeLocalization_sameShift_eq_iff
#print axioms LinearStudy.originalDegreeVeronesePrimeLocalization_sameShift_eq_iff

