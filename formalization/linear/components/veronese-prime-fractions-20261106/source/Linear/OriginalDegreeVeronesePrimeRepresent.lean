module
public import Linear.OriginalDegreeVeronesePrimeLocalization
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
local instance originalDegreeVeronesePrimeRepresentGraded : GradedAlgebra P :=
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

/-- Every original homogeneous fraction of shift q*k is represented by
a Veronese fraction of shift k at the exact contracted prime. -/
theorem originalDegreeVeronesePrimeLocalization_represents
    (x : Proj B) (k : ℤ) (n : ℕ) (b : B n)
    (hb : (b : S) ∉ x.asHomogeneousIdeal) (a : M)
    (ha : a ∈ D ((n : ℤ) + (q : ℤ)*k)) :
    ∃ s : Q x, ∃ y : W, (s : V) ∈ P n ∧
      (y : M) ∈ D ((q : ℤ)*((n : ℤ)+k)) ∧
      originalDegreeVeronesePrimeLocalization B q D hD x (LocalizedModule.mk y s) =
        LocalizedModule.mk a (⟨(b : S), hb⟩ : T x) := by
  let s := originalDegreeVeronesePrimeDenominatorPow B q x n b hb
  have hy := originalDegreeVeronesePromotedNumerator_mem B D hD q hq.out n k b b.property a ha
  let y : W := ⟨(b : S)^(q-1) • a,
    originalDegreeVeroneseCoefficient_mem_of_mem B D hD q ((n : ℤ)+k) hy⟩
  refine ⟨s, y, originalDegreeVeronesePrimeDenominatorPow_mem B q x n b hb, hy, ?_⟩
  rw [originalDegreeVeronesePrimeLocalization_mk]
  exact originalDegreeVeronesePromotedFraction_eq q hq.out (T x) ⟨(b : S), hb⟩ a

end LinearStudy
#check LinearStudy.originalDegreeVeronesePrimeLocalization_represents
#print axioms LinearStudy.originalDegreeVeronesePrimeLocalization_represents

