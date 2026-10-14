module
public import Linear.NativeHomogeneousMapRegrading
public import Linear.NativeProjectiveTwistRegrading
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
variable {K S M N : Type} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M]
variable [AddCommGroup N] [Module K N] [Module S N]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (D : ℤ → Submodule K M) (E : ℤ → Submodule K N)
variable (δ : ℤ) (e : M →ₗ[S] N)
variable (he : ∀ t : ℤ, ∀ x : M, x ∈ D t → e x ∈ E (t+δ))

include he

/-- Regrade ORIGINAL source by k and ORIGINAL target by k+delta.
The SAME original map is degree zero;this fact is proved from he. -/
theorem integerHomogeneousMap_two_regradings (k : ℤ) :
    ∀ t : ℤ, ∀ x : M, x ∈ integerGradingShift D k t →
      e x ∈ integerGradingShift E (k+δ) t := by
  intro t x hx
  simpa only [integerGradingShift,add_assoc] using he (t+k) x hx

variable (hD : ∀ t : ℕ, ∀ d : ℤ, ∀ p : S, p ∈ B t →
  ∀ x : M, x ∈ D d → p • x ∈ D ((t:ℤ)+d))
variable (hE : ∀ t : ℕ, ∀ d : ℤ, ∀ p : S, p ∈ B t →
  ∀ x : N, x ∈ E d → p • x ∈ E ((t:ℤ)+d))

/-- Regrading BOTH ORIGINAL modules at native twist zero gives the
SAME ORIGINAL degree-delta associated-sheaf map from M(k) to N(k+delta).
All ORIGINAL prime-localized values are retained,without map premises. -/
theorem nativeProjectiveHomogeneousMap_two_regradings (k : ℤ) :
    (nativeProjectiveTwistRegradingIso B D hD k).inv ≫
      nativeProjectiveDegreeZeroSheafMap B (integerGradingShift D k)
        (integerGradingShift E (k+δ))
        (integerGradingShift_smul_homogeneous B D hD k)
        (integerGradingShift_smul_homogeneous B E hE (k+δ))
        e (integerHomogeneousMap_two_regradings D E δ e he k) 0 ≫
      (nativeProjectiveTwistRegradingIso B E hE (k+δ)).hom =
    nativeProjectiveModuleSheafMap B D E hD hE δ e he k := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

end LinearStudy
