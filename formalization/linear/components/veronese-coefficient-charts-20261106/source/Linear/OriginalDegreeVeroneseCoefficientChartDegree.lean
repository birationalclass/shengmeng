module
public import Linear.OriginalDegreeVeroneseCoefficientGrading
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy

/-- The numerator degree on a regraded chart with an integer shift
matches its original degree exactly. -/
theorem originalDegreeVeroneseChartNumeratorDegree (q d n : ℕ) (k : ℤ) :
    (q : ℤ) * ((n : ℤ) * (d : ℤ) + k) =
      ((n * (q * d) : ℕ) : ℤ) + (q : ℤ) * k := by
  rw [mul_add, Nat.cast_mul, Nat.cast_mul, mul_left_comm (q : ℤ) (n : ℤ)]

universe u v w
variable {K : Type u} {S : Type v} {M : Type w}
variable [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (D : ℤ → Submodule K M)
variable (hD : ∀ (n : ℕ) (d : ℤ) (c : S), c ∈ B n →
  ∀ x : M, x ∈ D d → c • x ∈ D ((n : ℤ) + d))
variable (q : ℕ)
local notation "W" => originalDegreeVeroneseCoefficient B D hD q

theorem originalDegreeVeroneseChartNumerator_mem_iff
    (d n : ℕ) (k : ℤ) (a : W) :
    a ∈ originalDegreeVeroneseCoefficientPiece B D hD q ((n : ℤ) * (d : ℤ) + k) ↔
      (a : M) ∈ D (((n * (q * d) : ℕ) : ℤ) + (q : ℤ) * k) := by
  rw [originalDegreeVeroneseCoefficientPiece_mem_iff, originalDegreeVeroneseChartNumeratorDegree]

/-- Every numerator of the original chart degree comes from the regraded
coefficient with the same underlying value. -/
theorem originalDegreeVeroneseChartNumerator_exists
    (d n : ℕ) (k : ℤ) (a : M)
    (ha : a ∈ D (((n * (q * d) : ℕ) : ℤ) + (q : ℤ) * k)) :
    ∃ b : W, (b : M) = a ∧
      b ∈ originalDegreeVeroneseCoefficientPiece B D hD q ((n : ℤ) * (d : ℤ) + k) := by
  have ha' : a ∈ D ((q : ℤ) * ((n : ℤ) * (d : ℤ) + k)) :=
    (originalDegreeVeroneseChartNumeratorDegree q d n k).symm ▸ ha
  let b : W := ⟨a, originalDegreeVeroneseCoefficient_mem_of_mem B D hD q _ ha'⟩
  exact ⟨b, rfl, ha'⟩

end LinearStudy
#check LinearStudy.originalDegreeVeroneseChartNumeratorDegree
#print axioms LinearStudy.originalDegreeVeroneseChartNumeratorDegree
#check LinearStudy.originalDegreeVeroneseChartNumerator_mem_iff
#print axioms LinearStudy.originalDegreeVeroneseChartNumerator_mem_iff
#check LinearStudy.originalDegreeVeroneseChartNumerator_exists
#print axioms LinearStudy.originalDegreeVeroneseChartNumerator_exists

