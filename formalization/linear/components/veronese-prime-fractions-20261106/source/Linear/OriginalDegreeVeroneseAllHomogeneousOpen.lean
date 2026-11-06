module
public import Linear.OriginalDegreeVeroneseBasicOpen
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
local instance originalDegreeVeroneseAllHomogeneousOpenGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out
local notation "I" => OriginalDegreeVeroneseChartIndex B q
local notation "C" => originalDegreeVeroneseAmbientAffineCover B q
local notation "D" => originalDegreeVeroneseRegradedAffineCover B q
local notation "E" => originalDegreeVeroneseIndexedAffineIso B q
local notation "F" => originalDegreeVeroneseProjHom B q

local notation "V" => originalDegreeVeroneseAlgebra B q

private theorem projective_basicOpen_mul_cancel
    {L R T : Type*} [Field L] [CommRing R] [CommRing T]
    [Algebra L R] [Algebra L T]
    (A : ℕ → Submodule L R) [GradedAlgebra A]
    (A' : ℕ → Submodule L T) [GradedAlgebra A']
    (x : Proj A) (y : Proj A') (f g : R) (f' g' : T)
    (hg : x ∈ Proj.basicOpen A g) (hg' : y ∈ Proj.basicOpen A' g')
    (h : y ∈ Proj.basicOpen A' (f'*g') ↔ x ∈ Proj.basicOpen A (f*g)) :
    y ∈ Proj.basicOpen A' f' ↔ x ∈ Proj.basicOpen A f := by
  rw [Proj.basicOpen_mul, Proj.basicOpen_mul] at h
  exact ⟨fun hy => (h.mp ⟨hy,hg'⟩).1, fun hx => (h.mpr ⟨hx,hg⟩).1⟩

/-- Multiply an arbitrary homogeneous denominator by a positive one. -/
def originalDegreeVeroneseChartIndex_mul
    (i : I) {d : ℕ} {f : V} (hf : f ∈ P d) : I :=
  ⟨⟨d + (i.1 : ℕ), Nat.lt_of_lt_of_le i.1.2 (Nat.le_add_left _ _)⟩,
    f * i.2.1, SetLike.mul_mem_graded hf i.2.2⟩

/-- Membership is compared for every homogeneous denominator, including
degree zero by multiplying by a positive denominator at the point. -/
theorem originalDegreeVeroneseProjHom_mem_basicOpen_homogeneous
    {d : ℕ} {f : V} (hf : f ∈ P d) (x : Proj B) :
    F x ∈ Proj.basicOpen P f ↔ x ∈ Proj.basicOpen B (f : S) := by
  obtain ⟨i, hi⟩ := originalDegreeVeroneseAmbientIndex_exists B q x
  have hi' := (originalDegreeVeroneseProjHom_mem_basicOpen_iff B q i x).mpr hi
  exact projective_basicOpen_mul_cancel B P x (F x) (f : S) (i.2.1 : S)
    f i.2.1 hi hi' (originalDegreeVeroneseProjHom_mem_basicOpen_iff B q
      (originalDegreeVeroneseChartIndex_mul B q i hf) x)

/-- The established scheme isomorphism compares membership in the actual
homogeneous primes for each homogeneous element of the subalgebra. -/
theorem originalDegreeVeroneseProjHom_mem_prime_homogeneous
    {d : ℕ} {f : V} (hf : f ∈ P d) (x : Proj B) :
    f ∈ (F x).asHomogeneousIdeal ↔ (f : S) ∈ x.asHomogeneousIdeal := by
  simpa only [Proj.mem_basicOpen, not_iff_not] using
    (originalDegreeVeroneseProjHom_mem_basicOpen_homogeneous B q hf x)

end LinearStudy
#check LinearStudy.originalDegreeVeroneseProjHom_mem_basicOpen_homogeneous
#print axioms LinearStudy.originalDegreeVeroneseProjHom_mem_basicOpen_homogeneous
#check LinearStudy.originalDegreeVeroneseProjHom_mem_prime_homogeneous
#print axioms LinearStudy.originalDegreeVeroneseProjHom_mem_prime_homogeneous

