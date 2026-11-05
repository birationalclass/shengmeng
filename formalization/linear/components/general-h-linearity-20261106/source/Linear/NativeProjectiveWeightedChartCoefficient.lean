module
public import Linear.NativeGradedWeightedCoefficientMap
public import Linear.NativeProjectiveChartCoefficientValue
public import Linear.NativeProjectiveDegreeZeroMap
public import Linear.NativeProjectiveChartSections
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
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
/-- The ACTUAL original chart-to-section map commutes with the ORIGINAL
degree-zero coefficient map. All weighted denominators retain degree d. -/
theorem nativeProjectiveChartDegreeZeroSectionMap_coefficient (d : ℕ) (a : R) (ha : a ∈ A d)
    (x : nativeGradedModuleAwayDegreeZero A D d a) :
    nativeProjectiveDegreeZeroSectionMap A D E hD hE f hf 0 (op (Proj.basicOpen A a))
      (nativeProjectiveChartDegreeZeroSectionMap A D hD d a ha x) =
      nativeProjectiveChartDegreeZeroSectionMap A E hE d a ha
        (nativeGradedModuleAwayDegreeZeroCoefficientMap A D E hD f hf d a ha x) := by
  apply Subtype.ext
  funext p
  exact nativeProjectiveChartRefinement_coefficient A a f x.val p
end LinearStudy
