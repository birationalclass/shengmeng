module
public import Linear.OriginalGradedCoextensionAdjoint
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory
universe u
variable {K R S M : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable [AddCommGroup M] [Module R M] [Module S M] [Module K M]
variable [IsScalarTower R S M]
attribute [local instance] coextensionGradedBaseModule nativeCoextensionNormalizationBaseModule
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable [SetLike.GradedSMul A B]
variable (D : ℤ → Submodule K M)
variable (hS : ∀ n : ℕ,∀ j : ℤ,∀ s : S,s ∈ B n →
  ∀ x : M,x ∈ D j → s • x ∈ D ((n:ℤ)+j))
include hS in
/-- Only integer arithmetic is needed to recover the ORIGINAL degree-zero
coefficient map from the all-degree original adjunction theorem. -/
theorem coextensionOriginalAdjoint_degreeZero (d : ℤ) (hd : d=0)
    (phi : integerGradedHomPiece A D d) :
    ∀ j : ℤ,∀ x : M,x ∈ D j →
      coextensionOriginalAdjoint phi.1 x ∈ coextensionGradedPiece A B j := by
  intro j x hx
  simpa only [hd,add_zero] using
    coextensionOriginalAdjoint_homogeneous A B D hS d phi j x hx
end LinearStudy
