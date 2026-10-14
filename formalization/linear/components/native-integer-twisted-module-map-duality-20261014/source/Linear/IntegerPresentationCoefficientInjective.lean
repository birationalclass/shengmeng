module
public import Linear.IntegerShiftedFreePresentationDualCokernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
variable {K S I J M : Type} [Field K] [CommRing S] [Algebra K S]
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable [AddCommGroup M] [Module K M] [Module S M]
variable (c : (I → S) →ₗ[S] (J → S))
variable (B : ℕ → Submodule K S) [GradedAlgebra B] (z : I → ℤ) (w : J → ℤ)
variable (hc : ∀ d : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece B z d →
  c x ∈ integerShiftedFreePiece B w d)
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (β : (J → S) →ₗ[S] M)
variable (hβ : ∀ d : ℤ, ∀ x : J → S, x ∈ integerShiftedFreePiece B w d → β x ∈ D d)
variable (honto : Function.Surjective β) (hex : LinearMap.range c = LinearMap.ker β)

/-- The ORIGINAL coefficient evaluation is injective by the already
constructed actual original Hom/kernel equivalence. No dimension or
cohomological surjectivity condition is assumed. -/
theorem integerPresentationHomCoefficientMap_injective (d : ℤ) :
    Function.Injective (integerShiftedFreePresentationHomCoefficientMap c B z w hc
      D β hβ honto hex d) :=
  Subtype.val_injective.comp
    (integerShiftedFreePresentationHomPolynomialKernelEquiv c B z w hc D β hβ honto hex d).injective

end LinearStudy
