module
public import Linear.OriginalDegreeVeronesePrimeDenominator
public import Linear.IntegerGradedHomogeneousAnnihilator
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
local instance originalDegreeVeronesePrimeAnnihilatorGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out
local notation "V" => originalDegreeVeroneseAlgebra B q
local notation "F" => originalDegreeVeroneseProjHom B q

local notation "Q" => originalDegreeVeroneseRegradedPrimeCompl B q
local notation "T" => originalDegreeVeroneseAmbientPrimeCompl B

variable {M : Type w} [AddCommGroup M] [Module K M] [Module S M]
variable (D : ℤ → Submodule K M)
variable (hD : ∀ (n : ℕ) (d : ℤ) (c : S), c ∈ B n →
  ∀ a : M, a ∈ D d → c • a ∈ D ((n : ℤ) + d))

variable [DirectSum.Decomposition D]

include hD in
/-- A homogeneous original relation killed outside the original prime is
also killed by a denominator of the contracted Veronese prime. -/
theorem originalDegreeVeronesePrimeAnnihilator
    (x : Proj B) (d : ℤ) (a : M) (ha : a ∈ D d)
    (t : S) (ht : t ∉ x.asHomogeneousIdeal) (hta : t • a = 0) :
    ∃ s : Q x, ((s : V) : S) • a = 0 := by
  obtain ⟨n, c, hc, hca⟩ :=
    homogeneous_annihilator_outside_projectivePrime B D hD d a ha x t ht hta
  refine ⟨originalDegreeVeronesePrimeDenominatorPow B q x n c hc, ?_⟩
  change (c : S)^q • a = 0
  have hq' : q - 1 + 1 = q := Nat.sub_add_cancel hq.out
  rw [← hq', pow_succ, mul_smul, hca, smul_zero]

end LinearStudy
#check LinearStudy.originalDegreeVeronesePrimeAnnihilator
#print axioms LinearStudy.originalDegreeVeronesePrimeAnnihilator

