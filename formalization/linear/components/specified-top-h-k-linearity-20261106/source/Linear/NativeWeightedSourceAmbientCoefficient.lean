module
public import Linear.NativeBaseSourceWeightedCoefficientSections
public import Linear.NativeWeightedSourceAmbientSectionEquiv
public import Linear.SurjectiveCalibratedComparisonNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K R S M N : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable [AddCommGroup M] [Module K M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module K N] [Module R N] [Module S N] [IsScalarTower R S N]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (B : ℕ → Submodule K S) [GradedAlgebra B] [SetLike.GradedSMul A B]
variable (D : ℤ → Submodule K M) (E : ℤ → Submodule K N)
variable (hRD : ∀ n : ℕ,∀ j : ℤ,∀ z : R,z ∈ A n → ∀ x : M,x ∈ D j → z • x ∈ D ((n:ℤ)+j))
variable (hSD : ∀ n : ℕ,∀ j : ℤ,∀ z : S,z ∈ B n → ∀ x : M,x ∈ D j → z • x ∈ D ((n:ℤ)+j))
variable (hRE : ∀ n : ℕ,∀ j : ℤ,∀ z : R,z ∈ A n → ∀ x : N,x ∈ E j → z • x ∈ E ((n:ℤ)+j))
variable (hSE : ∀ n : ℕ,∀ j : ℤ,∀ z : S,z ∈ B n → ∀ x : N,x ∈ E j → z • x ∈ E ((n:ℤ)+j))
variable (f : M →ₗ[S] N) (hf : ∀ j : ℤ,∀ x : M,x ∈ D j → f x ∈ E j)
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
attribute [local irreducible] nativeWeightedSourceAmbientSectionAddEquiv
/-- The SAME weighted ambient/source section comparison is natural for
an ORIGINAL S-linear degree-zero coefficient map. The FOUR LOCAL chart
bijections are explicit here;finite graded applications derive them. -/
theorem nativeWeightedSourceAmbientSectionAddEquiv_coefficient
    (d : ℕ) (a : R) (ha : a ∈ A d)
    (hAM : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap A D hRD d a ha))
    (hBM : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap B D hSD d
      (algebraMap R S a) ((normalizationBaseGradedRingHom A B).map_mem ha)))
    (hAN : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap A E hRE d a ha))
    (hBN : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap B E hSE d
      (algebraMap R S a) ((normalizationBaseGradedRingHom A B).map_mem ha)))
    (x : nativeProjectiveModuleSections A D hRD 0 (op (Proj.basicOpen A a))) :
    nativeWeightedSourceAmbientSectionAddEquiv A B E hRE hSE d a ha hAN hBN
      (nativeProjectiveDegreeZeroSectionMap A D E hRD hRE (f.restrictScalars R) hf 0
        (op (Proj.basicOpen A a)) x) =
      nativeProjectiveDegreeZeroSectionMap B D E hSD hSE f hf 0
        (op (Proj.basicOpen B (algebraMap R S a)))
        (nativeWeightedSourceAmbientSectionAddEquiv A B D hRD hSD d a ha hAM hBM x) := by
  exact surjectiveCalibratedComparison_naturality
    (nativeProjectiveChartDegreeZeroSectionMap A D hRD d a ha)
    (nativeBaseSourceWeightedChartSection A B D (hR:=hRD) (hS:=hSD) d a ha)
    (nativeProjectiveChartDegreeZeroSectionMap A E hRE d a ha)
    (nativeBaseSourceWeightedChartSection A B E (hR:=hRE) (hS:=hSE) d a ha)
    (nativeWeightedSourceAmbientSectionAddEquiv A B D hRD hSD d a ha hAM hBM)
    (nativeWeightedSourceAmbientSectionAddEquiv A B E hRE hSE d a ha hAN hBN)
    (nativeGradedModuleAwayDegreeZeroCoefficientMap A D E hRD (f.restrictScalars R) hf d a ha)
    (nativeProjectiveDegreeZeroSectionMap A D E hRD hRE (f.restrictScalars R) hf 0 (op (Proj.basicOpen A a)))
    (nativeProjectiveDegreeZeroSectionMap B D E hSD hSE f hf 0 (op (Proj.basicOpen B (algebraMap R S a))))
    hAM.surjective
    (nativeWeightedSourceAmbientSectionAddEquiv_chart A B D hRD hSD d a ha hAM hBM)
    (nativeWeightedSourceAmbientSectionAddEquiv_chart A B E hRE hSE d a ha hAN hBN)
    (nativeProjectiveChartDegreeZeroSectionMap_coefficient A D E hRD hRE (f.restrictScalars R) hf d a ha)
    (nativeBaseSourceWeightedChartSection_coefficient A B D E hRD hSD hRE hSE f hf d a ha) x
end LinearStudy
