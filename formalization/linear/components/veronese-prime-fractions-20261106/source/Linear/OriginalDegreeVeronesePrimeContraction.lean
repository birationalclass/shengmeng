module
public import Linear.OriginalDegreeVeroneseAllHomogeneousOpen
public import Linear.GradedIdealContractionByDegrees
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
local instance originalDegreeVeronesePrimeContractionGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out
local notation "V" => originalDegreeVeroneseAlgebra B q
local notation "F" => originalDegreeVeroneseProjHom B q

/-- The point of the established scheme isomorphism is exactly contraction
of the original homogeneous prime to the Veronese subalgebra. -/
theorem originalDegreeVeroneseProjHom_prime_contraction (x : Proj B) :
    (F x).asHomogeneousIdeal.toIdeal =
      x.asHomogeneousIdeal.toIdeal.comap (V).val.toRingHom :=
  homogeneousIdeal_toIdeal_eq_comap_of_compare P B (V).val.toRingHom (q * ·)
    (fun _ _ h => Nat.mul_left_cancel hq.out h) (fun _ _ h => h)
    (F x).asHomogeneousIdeal x.asHomogeneousIdeal
    (fun _ _ h => originalDegreeVeroneseProjHom_mem_prime_homogeneous B q h x)

theorem originalDegreeVeroneseProjHom_mem_prime_iff (x : Proj B) (a : V) :
    a ∈ (F x).asHomogeneousIdeal ↔ (a : S) ∈ x.asHomogeneousIdeal := by
  change a ∈ (F x).asHomogeneousIdeal.toIdeal ↔ _
  rw [originalDegreeVeroneseProjHom_prime_contraction B q x]
  rfl

end LinearStudy
#check LinearStudy.originalDegreeVeroneseProjHom_prime_contraction
#print axioms LinearStudy.originalDegreeVeroneseProjHom_prime_contraction
#check LinearStudy.originalDegreeVeroneseProjHom_mem_prime_iff
#print axioms LinearStudy.originalDegreeVeroneseProjHom_mem_prime_iff

