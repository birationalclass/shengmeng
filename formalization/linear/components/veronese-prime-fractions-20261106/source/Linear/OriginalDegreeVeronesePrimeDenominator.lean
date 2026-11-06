module
public import Linear.OriginalDegreeVeronesePrimeContraction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u v
variable {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (q : ℕ) [hq : Fact (0 < q)]
local notation "P" => originalDegreeVeronesePiece B q
local instance originalDegreeVeronesePrimeDenominatorGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out
local notation "V" => originalDegreeVeroneseAlgebra B q
local notation "F" => originalDegreeVeroneseProjHom B q

/-- Prime denominators at the corresponding Veronese point. -/
abbrev originalDegreeVeroneseRegradedPrimeCompl (x : Proj B) : Submonoid V :=
  @Ideal.primeCompl V _ (F x).asHomogeneousIdeal.toIdeal (F x).isPrime

/-- Prime denominators at the original projective point. -/
abbrev originalDegreeVeroneseAmbientPrimeCompl (x : Proj B) : Submonoid S :=
  @Ideal.primeCompl S _ x.asHomogeneousIdeal.toIdeal x.isPrime

local notation "Q" => originalDegreeVeroneseRegradedPrimeCompl B q
local notation "T" => originalDegreeVeroneseAmbientPrimeCompl B

/-- Denominators from the contracted prime complement have the same
values in the original prime complement. -/
def originalDegreeVeronesePrimeDenominator (x : Proj B) (s : Q x) : T x :=
  ⟨((s : V) : S), (not_congr (originalDegreeVeroneseProjHom_mem_prime_iff B q x s)).mp s.property⟩

omit hq in
theorem originalDegreeVeronesePower_mem (n : ℕ) (b : B n) :
    (b : S)^q ∈ B (q*n) := by
  simpa only [nsmul_eq_mul, Nat.cast_id] using SetLike.pow_mem_graded q b.property

/-- The q-th power of a homogeneous original denominator belongs to
the exact contracted prime complement and has regraded degree n. -/
def originalDegreeVeronesePrimeDenominatorPow
    (x : Proj B) (n : ℕ) (b : B n) (hb : (b : S) ∉ x.asHomogeneousIdeal) : Q x := by
  let y : V := ⟨(b : S)^q, originalDegreeVeroneseAlgebra_mem_of_mem B q n
    (originalDegreeVeronesePower_mem B q n b)⟩
  have hy : (y : S) ∉ x.asHomogeneousIdeal :=
    pow_mem (show (b : S) ∈ T x from hb) q
  exact ⟨y, (not_congr (originalDegreeVeroneseProjHom_mem_prime_iff B q x y)).mpr hy⟩

theorem originalDegreeVeronesePrimeDenominatorPow_mem
    (x : Proj B) (n : ℕ) (b : B n) (hb : (b : S) ∉ x.asHomogeneousIdeal) :
    (originalDegreeVeronesePrimeDenominatorPow B q x n b hb : V) ∈ P n :=
  originalDegreeVeronesePower_mem B q n b

end LinearStudy
#check LinearStudy.originalDegreeVeronesePrimeDenominator
#print axioms LinearStudy.originalDegreeVeronesePrimeDenominator
#check LinearStudy.originalDegreeVeronesePrimeDenominatorPow
#print axioms LinearStudy.originalDegreeVeronesePrimeDenominatorPow
#check LinearStudy.originalDegreeVeronesePrimeDenominatorPow_mem
#print axioms LinearStudy.originalDegreeVeronesePrimeDenominatorPow_mem

