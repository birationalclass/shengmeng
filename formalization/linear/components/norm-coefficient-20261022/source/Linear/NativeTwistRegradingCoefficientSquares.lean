module
public import Linear.NativeProjectiveDegreeZeroMap
public import Linear.SchemeModuleFiniteSupportCohomology
public import Linear.NativeProjectiveTwistRegrading
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K R M N : Type u} [Field K] [CommRing R] [Algebra K R]
variable [AddCommGroup M] [Module R M] [Module K M]
variable [AddCommGroup N] [Module R N] [Module K N]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (D : ℤ → Submodule K M) (E : ℤ → Submodule K N)
variable (hD : ∀ n : ℕ,∀ j : ℤ,∀ z : R,z ∈ A n → ∀ x : M,x ∈ D j → z • x ∈ D ((n:ℤ)+j))
variable (hE : ∀ n : ℕ,∀ j : ℤ,∀ z : R,z ∈ A n → ∀ x : N,x ∈ E j → z • x ∈ E ((n:ℤ)+j))
variable (f : M →ₗ[R] N) (hf : ∀ j : ℤ,∀ x : M,x ∈ D j → f x ∈ E j)
attribute [local instance] nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
/-- Original regrading is natural for the ORIGINAL degree-zero coefficient
map on EVERY open. This is the two-object hom square,proved by the SAME
identity on prime-localized values used by the existing regrading proof. -/
theorem nativeProjectiveTwistRegradingIso_coefficient_hom (k : ℤ) :
    nativeProjectiveDegreeZeroSheafMap A (integerGradingShift D k) (integerGradingShift E k)
      (integerGradingShift_smul_homogeneous A D hD k)
      (integerGradingShift_smul_homogeneous A E hE k) f (fun j x hx => hf (j+k) x hx) 0 ≫
        (nativeProjectiveTwistRegradingIso A E hE k).hom =
    (nativeProjectiveTwistRegradingIso A D hD k).hom ≫
      nativeProjectiveDegreeZeroSheafMap A D E hD hE f hf k := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl
/-- The original inverse regrading square,for the SAME degree-zero map
and EVERY integer twist. No comparison or naturality certificate is assumed. -/
theorem nativeProjectiveTwistRegradingIso_coefficient_inv (k : ℤ) :
    nativeProjectiveDegreeZeroSheafMap A D E hD hE f hf k ≫
      (nativeProjectiveTwistRegradingIso A E hE k).inv =
    (nativeProjectiveTwistRegradingIso A D hD k).inv ≫
      nativeProjectiveDegreeZeroSheafMap A (integerGradingShift D k) (integerGradingShift E k)
        (integerGradingShift_smul_homogeneous A D hD k)
        (integerGradingShift_smul_homogeneous A E hE k) f (fun j x hx => hf (j+k) x hx) 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl
end LinearStudy
