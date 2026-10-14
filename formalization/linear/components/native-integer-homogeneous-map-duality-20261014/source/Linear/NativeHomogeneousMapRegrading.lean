module
public import Linear.NativeProjectiveShiftAtTwist
public import Linear.NativeProjectiveDegreeZeroMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K S M N : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M]
variable [AddCommGroup N] [Module K N] [Module S N]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (D : ℤ → Submodule K M) (E : ℤ → Submodule K N)
variable (hD : ∀ t : ℕ, ∀ d : ℤ, ∀ p : S, p ∈ B t →
  ∀ x : M, x ∈ D d → p • x ∈ D ((t:ℤ)+d))
variable (hE : ∀ t : ℕ, ∀ d : ℤ, ∀ p : S, p ∈ B t →
  ∀ x : N, x ∈ E d → p • x ∈ E ((t:ℤ)+d))
variable (δ : ℤ) (e : M →ₗ[S] N)
variable (he : ∀ t : ℤ, ∀ x : M, x ∈ D t → e x ∈ E (t+δ))

/-- The ORIGINAL degree-delta associated-sheaf map is the ACTUAL
original degree-zero map into E[delta],followed by the constructed
original integer-twist regrading iso. ALL original prime-localized
values and the original e are retained;no square is assumed. -/
theorem nativeProjectiveHomogeneousMap_regrade (k : ℤ) :
    nativeProjectiveDegreeZeroSheafMap B D (integerGradingShift E δ) hD
      (integerGradingShift_smul_homogeneous B E hE δ) e he k ≫
      (nativeProjectiveShiftAtTwistIso B E hE δ k).hom =
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
