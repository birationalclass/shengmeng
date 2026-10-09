module
public import Linear.CoextensionGradedBaseEquiv
public import Linear.GradedDecompositionTransport
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
namespace LinearStudy
open CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑]
attribute [local instance] coextensionGradedBaseModule

/-- Actual integer-degree pieces of the native normalization dual. -/
def coextensionGradedPiece (k : ℤ) :
    Submodule K ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) :=
  (gradedHomPiece (A := R) 𝓑 𝒜 k).comap
    (coextensionGradedBaseEquiv (K := K) (R := R) (S := S)).toLinearMap

theorem coextensionGradedPiece_mem_iff (k : ℤ)
    (ell : (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) :
    ell ∈ coextensionGradedPiece 𝒜 𝓑 k ↔
      ∀ n : ℕ, ∀ x : S, x ∈ 𝓑 n →
        ell x = gradedIntegerProjection 𝒜 ((n : ℤ)+k) (ell x) := Iff.rfl

/-- The actual native dual receives a constructed integer grading,
with its actual original scalar action, when S is finite over R. -/
@[instance_reducible] def coextensionGradedDecomposition [Module.Finite R S] :
    DirectSum.Decomposition (coextensionGradedPiece 𝒜 𝓑) := by
  letI := gradedHomDecomposition 𝒜 𝓑 𝒜
  exact transportedGrading (gradedHomPiece (A := R) 𝓑 𝒜)
    (coextensionGradedBaseEquiv (K := K) (R := R) (S := S))

/-- The ORIGINAL upper scalar multiplication is graded: precomposing
with multiplication by a degree-d element increases the dual degree by d. -/
theorem coextensionGradedPiece_smul_homogeneous (d : ℕ) (k : ℤ)
    (b : S) (hb : b ∈ 𝓑 d)
    (ell : (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))
    (hell : ell ∈ coextensionGradedPiece 𝒜 𝓑 k) :
    b • ell ∈ coextensionGradedPiece 𝒜 𝓑 (k+(d : ℤ)) := by
  rw [coextensionGradedPiece_mem_iff] at hell ⊢
  intro n x hx
  change ell (x*b) = gradedIntegerProjection 𝒜 ((n : ℤ)+(k+(d : ℤ))) (ell (x*b))
  have hxb : x*b ∈ 𝓑 (n+d) := SetLike.mul_mem_graded hx hb
  simpa only [Int.natCast_add,add_assoc,add_comm,add_left_comm] using
    hell (n+d) (x*b) hxb

end LinearStudy
