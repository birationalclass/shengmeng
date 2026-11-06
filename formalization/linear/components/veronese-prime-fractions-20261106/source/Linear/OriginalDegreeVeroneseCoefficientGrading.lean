module
public import Linear.OriginalDegreeVeroneseCoefficient
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
universe u v w
variable {K : Type u} {S : Type v} {M : Type w}
variable [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (D : ℤ → Submodule K M)
variable (hD : ∀ (n : ℕ) (d : ℤ) (c : S), c ∈ B n →
  ∀ x : M, x ∈ D d → c • x ∈ D ((n : ℤ) + d))
variable (q : ℕ)
local notation "V" => originalDegreeVeroneseAlgebra B q
local notation "W" => originalDegreeVeroneseCoefficient B D hD q

/-- Regraded integer piece, pulled back along the actual coefficient inclusion. -/
def originalDegreeVeroneseCoefficientPiece (j : ℤ) : Submodule K W :=
  (D ((q : ℤ) * j)).comap ((W).restrictScalars K).subtype

theorem originalDegreeVeroneseCoefficientPiece_mem_iff
    (j : ℤ) (x : W) :
    x ∈ originalDegreeVeroneseCoefficientPiece B D hD q j ↔
      (x : M) ∈ D ((q : ℤ) * j) := Iff.rfl

/-- The actual Veronese scalar action adds the regraded degrees. -/
theorem originalDegreeVeroneseCoefficient_smul_homogeneous
    (n : ℕ) (j : ℤ) (c : V)
    (hc : c ∈ originalDegreeVeronesePiece B q n)
    (x : W) (hx : x ∈ originalDegreeVeroneseCoefficientPiece B D hD q j) :
    c • x ∈ originalDegreeVeroneseCoefficientPiece B D hD q ((n : ℤ) + j) := by
  have hcS : (c : S) ∈ B (q * n) := hc
  have hxM : (x : M) ∈ D ((q : ℤ) * j) := hx
  change (c : S) • (x : M) ∈ D ((q : ℤ) * ((n : ℤ) + j))
  rw [mul_add, ← Nat.cast_mul]
  exact hD (q * n) ((q : ℤ) * j) (c : S) hcS (x : M) hxM

end LinearStudy
#check LinearStudy.originalDegreeVeroneseCoefficientPiece
#print axioms LinearStudy.originalDegreeVeroneseCoefficientPiece
#check LinearStudy.originalDegreeVeroneseCoefficientPiece_mem_iff
#print axioms LinearStudy.originalDegreeVeroneseCoefficientPiece_mem_iff
#check LinearStudy.originalDegreeVeroneseCoefficient_smul_homogeneous
#print axioms LinearStudy.originalDegreeVeroneseCoefficient_smul_homogeneous

