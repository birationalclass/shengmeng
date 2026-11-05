module
public import Linear.LocalizedOriginalKernelCoefficientZero
public import Linear.ActualChartQuotientZero
public import Linear.NativeGradedWeightedSurjection
public import Linear.NativeProjectiveWeightedChartCoefficient
public import Linear.NativeProjectiveKernelSectionExact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K R M N : Type u} [Field K] [CommRing R] [Algebra K R]
variable [AddCommGroup M] [Module R M] [Module K M] [IsScalarTower K R M]
variable [AddCommGroup N] [Module R N] [Module K N]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (D : ℤ → Submodule K M) (E : ℤ → Submodule K N)
variable [DirectSum.Decomposition D] [DirectSum.Decomposition E]
variable (hD : ∀ n : ℕ,∀ j : ℤ,∀ z : R,z ∈ A n → ∀ x : M,x ∈ D j → z • x ∈ D ((n:ℤ)+j))
variable (hE : ∀ n : ℕ,∀ j : ℤ,∀ z : R,z ∈ A n → ∀ x : N,x ∈ E j → z • x ∈ E ((n:ℤ)+j))
variable (f : M →ₗ[R] N) (hf : ∀ j : ℤ,∀ x : M,x ∈ D j → f x ∈ E j)
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
attribute [local irreducible] nativeProjectiveChartDegreeZeroSectionMap nativeProjectiveDegreeZeroSectionMap
include hf
/-- Actual localized kernel coefficients compose to zero. -/
theorem nativeGradedModuleAwayDegreeZeroCoefficientMap_kernel_zero
    (d : ℕ) (a : R) (ha : a ∈ A d)
    (w : nativeGradedModuleAwayDegreeZero A (nativeProjectiveKernelPiece D f) d a) :
    nativeGradedModuleAwayDegreeZeroCoefficientMap A D E hD f hf d a ha
      (nativeGradedModuleAwayDegreeZeroCoefficientMap A (nativeProjectiveKernelPiece D f) D
        (nativeProjectiveKernelPiece_graded A D f hD) f.ker.subtype
          (fun _ _ hx => hx) d a ha w) = 0 := by
  apply Subtype.ext
  exact localizedOriginalKernelCoefficient_comp_zero f a w.val
include hf
/-- Actual quotient chart zero is detected by its original native section,
using the actual source and kernel charts. -/
theorem nativeProjectiveChartDegreeZeroSectionMap_zero_of_kernel
    (he : Function.Surjective f) (d : ℕ) (a : R) (ha : a ∈ A d)
    (hsource : Function.Injective (nativeProjectiveChartDegreeZeroSectionMap A D hD d a ha))
    (hkernel : Function.Surjective (nativeProjectiveChartDegreeZeroSectionMap A
      (nativeProjectiveKernelPiece D f) (nativeProjectiveKernelPiece_graded A D f hD) d a ha))
    (x : nativeGradedModuleAwayDegreeZero A E d a)
    (hx : nativeProjectiveChartDegreeZeroSectionMap A E hE d a ha x = 0) : x = 0 := by
  let DK := nativeProjectiveKernelPiece D f
  let hK := nativeProjectiveKernelPiece_graded A D f hD
  let U := op (Proj.basicOpen A a)
  exact actualChartQuotient_zero
    (nativeGradedModuleAwayDegreeZeroCoefficientMap A D E hD f hf d a ha)
    (nativeProjectiveChartDegreeZeroSectionMap A D hD d a ha)
    (nativeProjectiveChartDegreeZeroSectionMap A E hE d a ha)
    (nativeProjectiveDegreeZeroSectionMap A D E hD hE f hf 0 U)
    (nativeGradedModuleAwayDegreeZeroCoefficientMap A DK D hK f.ker.subtype
      (fun _ _ hx => hx) d a ha)
    (nativeProjectiveDegreeZeroSectionMap A DK D hK hD f.ker.subtype (fun _ _ hx => hx) 0 U)
    (nativeProjectiveChartDegreeZeroSectionMap A DK hK d a ha) 0 0
    (nativeGradedModuleAwayDegreeZeroCoefficientMap_surjective A D E hD hE f hf he d a ha)
    hsource hkernel
    (fun y hy => (nativeProjectiveKernelSectionMap_exact A D E hD hE f hf 0 U y).mp hy)
    (fun y => (nativeProjectiveChartDegreeZeroSectionMap_coefficient A D E hD hE f hf d a ha y).symm)
    (fun y => (nativeProjectiveChartDegreeZeroSectionMap_coefficient A DK D hK hD f.ker.subtype
      (fun _ _ hx => hx) d a ha y).symm)
    (nativeGradedModuleAwayDegreeZeroCoefficientMap_kernel_zero A D E hD f hf d a ha) x hx
/-- Descent of actual chart injectivity along an original graded surjection. -/
theorem nativeProjectiveChartDegreeZeroSectionMap_injective_of_kernel
    (he : Function.Surjective f) (d : ℕ) (a : R) (ha : a ∈ A d)
    (hsource : Function.Injective (nativeProjectiveChartDegreeZeroSectionMap A D hD d a ha))
    (hkernel : Function.Surjective (nativeProjectiveChartDegreeZeroSectionMap A
      (nativeProjectiveKernelPiece D f) (nativeProjectiveKernelPiece_graded A D f hD) d a ha)) :
    Function.Injective (nativeProjectiveChartDegreeZeroSectionMap A E hE d a ha) :=
  (injective_iff_map_eq_zero (nativeProjectiveChartDegreeZeroSectionMap A E hE d a ha)).mpr
    (nativeProjectiveChartDegreeZeroSectionMap_zero_of_kernel A D E hD hE f hf he d a ha hsource hkernel)
end LinearStudy
