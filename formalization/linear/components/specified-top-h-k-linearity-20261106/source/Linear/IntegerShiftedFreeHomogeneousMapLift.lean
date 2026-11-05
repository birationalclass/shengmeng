module
public import Linear.IntegerGradedSurjectionPreimage
public import Linear.IntegerShiftedFreeGeneratorMap
public import Linear.IntegerShiftedFreeHomCoordinates
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
variable {K S I J M : Type} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M]
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (u : I → ℤ) (v : J → ℤ)
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (a : (I → S) →ₗ[S] M) (β : (J → S) →ₗ[S] M)
variable (ha : ∀ d : ℤ, ∀ x : I → S,
  x ∈ integerShiftedFreePiece B u d → a x ∈ D d)
variable (hβ : ∀ d : ℤ, ∀ x : J → S,
  x ∈ integerShiftedFreePiece B v d → β x ∈ D d)
variable (honto : Function.Surjective β)
include ha hβ honto

/-- Construct an ACTUAL degree-zero lift of an ORIGINAL homogeneous map
from a finite INTEGER shifted-free family through an ORIGINAL graded
surjection. Existing actual homogeneous preimages and original free
generator map are reused. No lift or comparison square is assumed. -/
theorem integerShiftedFree_exists_homogeneous_lift :
    ∃ τ : (I → S) →ₗ[S] (J → S),
      (∀ d : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece B u d →
        τ x ∈ integerShiftedFreePiece B v d) ∧ β.comp τ=a := by
  classical
  letI := integerShiftedFreeDecomposition B v
  have hlifts : ∀ i : I, ∃ x : J → S,
      x ∈ integerShiftedFreePiece B v (u i) ∧ β x=a (Pi.single i (1:S)) := by
    intro i
    exact integerDegreeZeroSurjection_homogeneous_preimages
      (integerShiftedFreePiece B v) D β hβ honto (u i) (a (Pi.single i 1))
      (ha (u i) (Pi.single i 1) (integerShiftedFree_single_one_mem B u i))
  choose lifts hL hVal using hlifts
  refine ⟨integerShiftedFreeGeneratorMap (S := S) lifts,?_,?_⟩
  · exact integerShiftedFreeGeneratorMap_homogeneous B
      (integerShiftedFreePiece B v) (integerShiftedFreePiece_smul_homogeneous B v) u lifts hL
  · apply (Pi.basisFun S I).ext
    intro i
    simp only [LinearMap.comp_apply,Pi.basisFun_apply,
      integerShiftedFreeGeneratorMap_single,one_smul,hVal]

end LinearStudy
