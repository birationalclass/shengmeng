module
public import Linear.IntegerGradedHomPrecomposition
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
variable {K S M : Type} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (D : ℤ → Submodule K M)
/-- Actual precomposition by the original identity fixes every homogeneous
functional,with the same integer degree. No duality input occurs. -/
theorem integerGradedHomPrecomposition_id (d : ℤ) :
    integerGradedHomPrecomposition B D D (LinearMap.id : M →ₗ[S] M)
      (fun _ _ hx => hx) d = LinearMap.id := by
  apply LinearMap.ext
  intro phi
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  rfl
end LinearStudy
