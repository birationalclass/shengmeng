module
public import Linear.OriginalDegreeVeronesePrimeRepresent
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
local instance originalDegreeVeronesePrimeFractionSetsGraded : GradedAlgebra P :=
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

/-- Actual values of homogeneous fractions at the original prime, of shift q*k. -/
def originalDegreeVeroneseAmbientPrimeFractions (x : Proj B) (k : ℤ) :
    Set (LocalizedModule (T x) M) :=
  {z | ∃ (n : ℕ) (b : B n) (hb : (b : S) ∉ x.asHomogeneousIdeal) (a : M),
    a ∈ D ((n : ℤ)+(q : ℤ)*k) ∧ z = LocalizedModule.mk a (⟨b,hb⟩ : T x)}

include hD in
/-- Actual values of homogeneous fractions of shift k at the contracted prime. -/
def originalDegreeVeroneseRegradedPrimeFractions (x : Proj B) (k : ℤ) :
    Set (LocalizedModule (Q x) W) :=
  {z | ∃ (n : ℕ) (s : Q x) (a : W), (s : V) ∈ P n ∧
    (a : M) ∈ D ((q : ℤ)*((n : ℤ)+k)) ∧ z = LocalizedModule.mk a s}

include hD in
/-- Every homogeneous fraction value on the original side has a regraded representative. -/
theorem originalDegreeVeronesePrimeLocalization_surjOn
    (x : Proj B) (k : ℤ) :
    Set.SurjOn (originalDegreeVeronesePrimeLocalization B q D hD x)
      (originalDegreeVeroneseRegradedPrimeFractions B q D hD x k)
      (originalDegreeVeroneseAmbientPrimeFractions B q D x k) := by
  rintro z ⟨n,b,hb,a,ha,rfl⟩
  obtain ⟨s,y,hs,hy,h⟩ := originalDegreeVeronesePrimeLocalization_represents B q D hD x k n b hb a ha
  exact ⟨LocalizedModule.mk y s, ⟨n,s,y,hs,hy,rfl⟩, h⟩

private theorem prime_fraction_grade (q n : ℕ) (k : ℤ) :
    (q : ℤ)*((n : ℤ)+k) = (↑(q*n) : ℤ) + (q : ℤ)*k := by
  rw [Nat.cast_mul, mul_add]

include hD in
/-- The regraded fraction map lands in the original fraction set of the precise shift. -/
theorem originalDegreeVeronesePrimeLocalization_mapsTo
    (x : Proj B) (k : ℤ) :
    Set.MapsTo (originalDegreeVeronesePrimeLocalization B q D hD x)
      (originalDegreeVeroneseRegradedPrimeFractions B q D hD x k)
      (originalDegreeVeroneseAmbientPrimeFractions B q D x k) := by
  rintro z ⟨n,s,a,hs,ha,rfl⟩
  let t := originalDegreeVeronesePrimeDenominator B q x s
  have hA : (a : M) ∈ D ((↑(q*n) : ℤ) + (q : ℤ)*k) :=
    (congrArg (fun d : ℤ => (a : M) ∈ D d) (prime_fraction_grade q n k)).mp ha
  refine ⟨q*n, ⟨(t : S),hs⟩, t.property, (a : M), hA, ?_⟩
  exact originalDegreeVeronesePrimeLocalization_mk B q D hD x a s

end LinearStudy
#check LinearStudy.originalDegreeVeroneseAmbientPrimeFractions
#print axioms LinearStudy.originalDegreeVeroneseAmbientPrimeFractions
#check LinearStudy.originalDegreeVeroneseRegradedPrimeFractions
#print axioms LinearStudy.originalDegreeVeroneseRegradedPrimeFractions
#check LinearStudy.originalDegreeVeronesePrimeLocalization_surjOn
#print axioms LinearStudy.originalDegreeVeronesePrimeLocalization_surjOn
#check LinearStudy.originalDegreeVeronesePrimeLocalization_mapsTo
#print axioms LinearStudy.originalDegreeVeronesePrimeLocalization_mapsTo

