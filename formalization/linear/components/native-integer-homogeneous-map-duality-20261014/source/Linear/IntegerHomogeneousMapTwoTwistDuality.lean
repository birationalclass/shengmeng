module
public import Linear.IntegerHomogeneousMapPrecomposition
public import Linear.NativeHomogeneousMapTwoTwists
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

/-- For ORIGINAL source twist k and ORIGINAL target twist k+delta,
precompose ORIGINAL homogeneous functionals from degree d-(k+delta)
to degree d-k. Every actual original phi(e(x)) is retained. -/
def integerGradedHomBetweenTwistsPrecomposition (d k : ℤ) :
    integerGradedHomPiece B E (d-(k+δ)) →ₗ[K] integerGradedHomPiece B D (d-k) :=
  ((e.dualMap.restrictScalars K).domRestrict
    (integerGradedHomPiece B E (d-(k+δ)))).codRestrict
    (integerGradedHomPiece B D (d-k)) (fun φ => by
      intro t x hx
      change φ.1 (e x) ∈ nativeProjectiveRingIntegerPiece B (t+(d-k))
      have hv := φ.property (t+δ) (e x) (he t x hx)
      have ha : (t+δ)+(d-(k+δ))=t+(d-k) := by omega
      simpa only [ha] using hv)

theorem integerGradedHomBetweenTwistsPrecomposition_apply (d k : ℤ)
    (φ : integerGradedHomPiece B E (d-(k+δ))) (x : M) :
    (integerGradedHomBetweenTwistsPrecomposition B D E δ e he d k φ).1 x=φ.1 (e x) := rfl

/-- Both ACTUAL ORIGINAL Hom regrading maps commute with the SAME
original homogeneous e. This PROVES the comparison transport square;
no duality square,degree transport certificate or chosen phi is assumed. -/
theorem integerGradedHomBetweenTwistsPrecomposition_regrade (d k : ℤ) :
    (integerGradedHomRegradingEquiv B D k d).toLinearMap.comp
      (integerGradedHomPrecomposition B (integerGradingShift D k)
        (integerGradingShift E (k+δ)) e
        (integerHomogeneousMap_two_regradings D E δ e he k) d) =
    (integerGradedHomBetweenTwistsPrecomposition B D E δ e he d k).comp
      (integerGradedHomRegradingEquiv B E (k+δ) d).toLinearMap := by
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  rfl

end LinearStudy
