module
public import Linear.IntegerGradedHomPrecomposition
public import Linear.IntegerShiftedFreeRegradingPresentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
variable {K S M N : Type} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M]
variable [AddCommGroup N] [Module K N] [Module S N]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (D : ℤ → Submodule K M) (E : ℤ → Submodule K N)
variable (δ : ℤ) (e : M →ₗ[S] N)
variable (he : ∀ t : ℤ, ∀ x : M, x ∈ D t → e x ∈ E (t+δ))

/-- Precompose by the ORIGINAL degree-delta map e. The ORIGINAL homogeneous
Hom degree changes from d-delta to d; every actual phi(e(x)) is retained. -/
def integerGradedHomHomogeneousPrecomposition (d : ℤ) :
    integerGradedHomPiece B E (d-δ) →ₗ[K] integerGradedHomPiece B D d :=
  ((e.dualMap.restrictScalars K).domRestrict (integerGradedHomPiece B E (d-δ))).codRestrict
    (integerGradedHomPiece B D d) (fun φ => by
      intro t x hx
      change φ.1 (e x) ∈ nativeProjectiveRingIntegerPiece B (t+d)
      have hv := φ.property (t+δ) (e x) (he t x hx)
      have ha : (t+δ)+(d-δ)=t+d := by omega
      simpa only [ha] using hv)

/-- This is the same original S-linear functional evaluated on e(x). -/
theorem integerGradedHomHomogeneousPrecomposition_apply (d : ℤ)
    (φ : integerGradedHomPiece B E (d-δ)) (x : M) :
    (integerGradedHomHomogeneousPrecomposition B D E δ e he d φ).1 x=φ.1 (e x) := rfl

/-- Actual degree-delta precomposition is obtained from the VERIFIED
original degree-zero map on E[delta],using the existing ORIGINAL Hom
regrading. This is an actual map equality,not a naturality premise. -/
theorem integerGradedHomHomogeneousPrecomposition_regrade (d : ℤ) :
    (integerGradedHomHomogeneousPrecomposition B D E δ e he d).comp
      (integerGradedHomRegradingEquiv B E δ d).toLinearMap =
    integerGradedHomPrecomposition B D (integerGradingShift E δ) e he d := by
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  rfl

end LinearStudy
