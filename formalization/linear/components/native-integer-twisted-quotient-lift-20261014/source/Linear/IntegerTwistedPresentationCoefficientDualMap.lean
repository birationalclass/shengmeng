module
public import Linear.IntegerShiftedFreeDualRegrading
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open CategoryTheory
variable {K S I J M : Type} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable [AddCommGroup M] [Module K M] [Module S M]
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (z : I → ℤ) (w : J → ℤ)
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (c : (I → S) →ₗ[S] (J → S)) (β : (J → S) →ₗ[S] M)
variable (hc : ∀ d : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece B z d →
  c x ∈ integerShiftedFreePiece B w d)
variable (hβ : ∀ d : ℤ, ∀ x : J → S, x ∈ integerShiftedFreePiece B w d → β x ∈ D d)
variable (honto : Function.Surjective β) (hex : LinearMap.range c = LinearMap.ker β)
attribute [local instance] integerGradingShiftDecomposition

/-- The ACTUAL dual of ORIGINAL coefficient evaluation commutes with
all integer regradings. This uses phi(beta(e_j)),not an assumed map or
an arbitrary isomorphism. It is the exact contravariant map square. -/
theorem integerTwistedPresentationCoefficientDualMap (k d : ℤ) :
    ModuleCat.ofHom (integerShiftedFreePresentationHomCoefficientMap c B
      (fun i => z i-k) (fun j => w j-k) (integerShiftedFreeRelation_regrade B z w c hc k)
      (integerGradingShift D k) β (integerShiftedFreeQuotient_regrade B w D β hβ k)
      honto hex d).dualMap ≫
      (integerGradedHomRegradingEquiv B D k d).dualMap.toModuleIso.inv =
    (integerShiftedFreeDualCoordinateRegradingEquiv B w k d).dualMap.toModuleIso.inv ≫
      ModuleCat.ofHom (integerShiftedFreePresentationHomCoefficientMap c B
        z w hc D β hβ honto hex (d-k)).dualMap := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ell
  apply LinearMap.ext
  intro φ
  change ell (integerShiftedFreePresentationHomCoefficientMap c B
    (fun i => z i-k) (fun j => w j-k) (integerShiftedFreeRelation_regrade B z w c hc k)
    (integerGradingShift D k) β (integerShiftedFreeQuotient_regrade B w D β hβ k)
    honto hex d ((integerGradedHomRegradingEquiv B D k d).symm φ)) =
      ell ((integerShiftedFreeDualCoordinateRegradingEquiv B w k d).symm
        (integerShiftedFreePresentationHomCoefficientMap c B z w hc D β hβ honto hex (d-k) φ))
  congr 1


end LinearStudy
