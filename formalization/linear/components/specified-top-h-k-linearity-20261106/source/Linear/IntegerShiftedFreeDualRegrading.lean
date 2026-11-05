module
public import Linear.IntegerShiftedFreeRegradingPresentation
public import Linear.IntegerShiftedFreePresentationDualCokernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
variable {K S I J M : Type} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]

/-- ORIGINAL polynomial Hom-coordinate tuples regrade by d-k. This is
actual equality of original Submodule.pi pieces,including negative pieces. -/
theorem integerShiftedFreeDualCoordinatePiece_regrade (w : J → ℤ) (k d : ℤ) :
    integerShiftedFreeDualCoordinatePiece B (fun j => w j-k) d =
      integerShiftedFreeDualCoordinatePiece B w (d-k) := by
  unfold integerShiftedFreeDualCoordinatePiece
  congr 1
  funext j
  congr 1
  dsimp only
  omega

/-- Original polynomial coefficient tuple transport,with unchanged values. -/
def integerShiftedFreeDualCoordinateRegradingEquiv (w : J → ℤ) (k d : ℤ) :
    integerShiftedFreeDualCoordinatePiece B (fun j => w j-k) d ≃ₗ[K]
      integerShiftedFreeDualCoordinatePiece B w (d-k) :=
  LinearEquiv.ofEq _ _ (integerShiftedFreeDualCoordinatePiece_regrade B w k d)

theorem integerShiftedFreeDualCoordinateRegradingEquiv_apply (w : J → ℤ) (k d : ℤ)
    (x : integerShiftedFreeDualCoordinatePiece B (fun j => w j-k) d) :
    (integerShiftedFreeDualCoordinateRegradingEquiv B w k d x).1=x.1 := rfl

variable [AddCommGroup M] [Module K M] [Module S M]

theorem integerGradedHomRegradingEquiv_symm_apply (D : ℤ → Submodule K M) (k d : ℤ)
    (φ : integerGradedHomPiece B D (d-k)) :
    ((integerGradedHomRegradingEquiv B D k d).symm φ).1=φ.1 := rfl

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (z : I → ℤ) (w : J → ℤ)
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (c : (I → S) →ₗ[S] (J → S)) (β : (J → S) →ₗ[S] M)
variable (hc : ∀ d : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece B z d →
  c x ∈ integerShiftedFreePiece B w d)
variable (hβ : ∀ d : ℤ, ∀ x : J → S, x ∈ integerShiftedFreePiece B w d → β x ∈ D d)
variable (honto : Function.Surjective β) (hex : LinearMap.range c = LinearMap.ker β)
attribute [local instance] integerGradingShiftDecomposition

/-- The ORIGINAL presentation coefficient map phi(beta(e_j)) commutes
with every INTEGER regrading. Original c,beta and every polynomial value
are unchanged. Neither coordinate-map compatibility nor a duality square
is supplied as a premise. -/
theorem integerShiftedFreePresentationHomCoefficientMap_regrade (k d : ℤ)
    (φ : integerGradedHomPiece B D (d-k)) :
    integerShiftedFreeDualCoordinateRegradingEquiv B w k d
      (integerShiftedFreePresentationHomCoefficientMap c B (fun i => z i-k)
        (fun j => w j-k) (integerShiftedFreeRelation_regrade B z w c hc k)
        (integerGradingShift D k) β (integerShiftedFreeQuotient_regrade B w D β hβ k)
        honto hex d ((integerGradedHomRegradingEquiv B D k d).symm φ)) =
      integerShiftedFreePresentationHomCoefficientMap c B z w hc D β hβ honto hex (d-k) φ := by
  apply Subtype.ext
  funext j
  rw [integerShiftedFreeDualCoordinateRegradingEquiv_apply]
  rw [integerShiftedFreePresentationHomCoefficientMap_apply,
    integerShiftedFreePresentationHomCoefficientMap_apply,
    integerGradedHomRegradingEquiv_symm_apply]

end LinearStudy
