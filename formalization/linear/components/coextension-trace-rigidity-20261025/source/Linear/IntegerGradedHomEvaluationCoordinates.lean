module
public import Linear.IntegerShiftedFreePresentationDualCokernel
public import Linear.IntegerGradedHomPrecomposition
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
variable {K S I J M : Type} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M]
variable [Fintype J] [DecidableEq J]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (w : J → ℤ) (D : ℤ → Submodule K M)
variable (β : (J → S) →ₗ[S] M)
variable (hβ : ∀ t : ℤ, ∀ x : J → S, x ∈ integerShiftedFreePiece B w t → β x ∈ D t)

/-- Direct ORIGINAL coefficient evaluation phi(beta(e_j)),using actual
original polynomial degree pieces. No presentation/kernel or duality
certificate is required to define this actual K-linear map. -/
def integerGradedHomEvaluationCoordinates (d : ℤ) :
    integerGradedHomPiece B D d →ₗ[K] integerShiftedFreeDualCoordinatePiece B w d where
  toFun φ := ⟨fun j => φ.1 (β (Pi.single j (1:S))),by
    intro j hj
    exact φ.property (w j) (β (Pi.single j 1))
      (hβ (w j) (Pi.single j 1) (integerShiftedFree_single_one_mem B w j))⟩
  map_add' φ ψ := by apply Subtype.ext; rfl
  map_smul' a φ := by apply Subtype.ext; rfl

theorem integerGradedHomEvaluationCoordinates_apply (d : ℤ)
    (φ : integerGradedHomPiece B D d) (j : J) :
    (integerGradedHomEvaluationCoordinates B w D β hβ d φ).1 j =
      φ.1 (β (Pi.single j (1:S))) := rfl

variable [Fintype I] [DecidableEq I] [DirectSum.Decomposition D]
variable (z : I → ℤ) (c : (I → S) →ₗ[S] (J → S))
variable (hc : ∀ t : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece B z t →
  c x ∈ integerShiftedFreePiece B w t)
variable (honto : Function.Surjective β) (hex : LinearMap.range c = LinearMap.ker β)

/-- The EXISTING constructed original Hom/kernel coefficient map is
EXACTLY direct original evaluation. The matrix/kernel construction and
all original values are retained;only the expression is simplified. -/
theorem integerPresentationHomCoefficientMap_eq_evaluation (d : ℤ) :
    integerShiftedFreePresentationHomCoefficientMap c B z w hc D β hβ honto hex d =
      integerGradedHomEvaluationCoordinates B w D β hβ d := by
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  funext j
  rw [integerShiftedFreePresentationHomCoefficientMap_apply,
    integerGradedHomEvaluationCoordinates_apply]

end LinearStudy
