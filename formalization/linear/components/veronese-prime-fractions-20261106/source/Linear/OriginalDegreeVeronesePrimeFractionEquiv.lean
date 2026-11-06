module
public import Linear.OriginalDegreeVeronesePrimeFractionSets
public import Linear.OriginalDegreeVeronesePrimeSameShift
public import Mathlib.Logic.Equiv.Set
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
local instance originalDegreeVeronesePrimeFractionEquivGraded : GradedAlgebra P :=
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

variable [DirectSum.Decomposition D]
include hD in
/-- Two regraded fractions of shift k with equal original values are equal. -/
theorem originalDegreeVeronesePrimeLocalization_injOn
    (x : Proj B) (k : ℤ) :
    Set.InjOn (originalDegreeVeronesePrimeLocalization B q D hD x)
      (originalDegreeVeroneseRegradedPrimeFractions B q D hD x k) := by
  rintro z ⟨d,s,a,hs,ha,rfl⟩ z' ⟨e,t,b,ht,hb,rfl⟩ h
  exact (originalDegreeVeronesePrimeLocalization_sameShift_eq_iff B q D hD x k a b s t
    hs ht ha hb).mp h

include hD in
/-- At corresponding primes the actual homogeneous fraction value sets are in bijection. -/
theorem originalDegreeVeronesePrimeLocalization_bijOn
    (x : Proj B) (k : ℤ) :
    Set.BijOn (originalDegreeVeronesePrimeLocalization B q D hD x)
      (originalDegreeVeroneseRegradedPrimeFractions B q D hD x k)
      (originalDegreeVeroneseAmbientPrimeFractions B q D x k) :=
  ⟨originalDegreeVeronesePrimeLocalization_mapsTo B q D hD x k,
    originalDegreeVeronesePrimeLocalization_injOn B q D hD x k,
    originalDegreeVeronesePrimeLocalization_surjOn B q D hD x k⟩

/-- The type equivalence has the actual prime-localization comparison as its forward map. -/
def originalDegreeVeronesePrimeFractionEquiv (x : Proj B) (k : ℤ) :
    (originalDegreeVeroneseRegradedPrimeFractions B q D hD x k) ≃
      (originalDegreeVeroneseAmbientPrimeFractions B q D x k) :=
  Set.BijOn.equiv _ (originalDegreeVeronesePrimeLocalization_bijOn B q D hD x k)

theorem originalDegreeVeronesePrimeFractionEquiv_val (x : Proj B) (k : ℤ)
    (z : originalDegreeVeroneseRegradedPrimeFractions B q D hD x k) :
    ((originalDegreeVeronesePrimeFractionEquiv B q D hD x k z) :
      LocalizedModule (T x) M) = originalDegreeVeronesePrimeLocalization B q D hD x z := rfl

end LinearStudy
#check LinearStudy.originalDegreeVeronesePrimeLocalization_injOn
#print axioms LinearStudy.originalDegreeVeronesePrimeLocalization_injOn
#check LinearStudy.originalDegreeVeronesePrimeLocalization_bijOn
#print axioms LinearStudy.originalDegreeVeronesePrimeLocalization_bijOn
#check LinearStudy.originalDegreeVeronesePrimeFractionEquiv
#print axioms LinearStudy.originalDegreeVeronesePrimeFractionEquiv
#check LinearStudy.originalDegreeVeronesePrimeFractionEquiv_val
#print axioms LinearStudy.originalDegreeVeronesePrimeFractionEquiv_val

