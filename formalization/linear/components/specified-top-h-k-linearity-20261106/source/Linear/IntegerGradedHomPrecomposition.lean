module
public import Linear.ActualPresentationGradedDualKernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
variable {K S M N : Type} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M]
variable [AddCommGroup N] [Module K N] [Module S N]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (D : ℤ → Submodule K M) (E : ℤ → Submodule K N)
variable (e : M →ₗ[S] N)
variable (he : ∀ t : ℤ, ∀ x : M, x ∈ D t → e x ∈ E t)

/-- Precompose an ORIGINAL homogeneous S-linear functional with the
ORIGINAL degree-zero module map. The actual original Hom pieces are used;
no cohomology-map or duality comparison is an input. -/
def integerGradedHomPrecomposition (d : ℤ) :
    integerGradedHomPiece B E d →ₗ[K] integerGradedHomPiece B D d :=
  ((e.dualMap.restrictScalars K).domRestrict (integerGradedHomPiece B E d)).codRestrict
    (integerGradedHomPiece B D d) (fun φ => by
      intro t x hx
      exact φ.property t (e x) (he t x hx))

/-- Preserve the ACTUAL ORIGINAL value phi(e(x)). -/
theorem integerGradedHomPrecomposition_apply (d : ℤ)
    (φ : integerGradedHomPiece B E d) (x : M) :
    (integerGradedHomPrecomposition B D E e he d φ).1 x=φ.1 (e x) := rfl

end LinearStudy
