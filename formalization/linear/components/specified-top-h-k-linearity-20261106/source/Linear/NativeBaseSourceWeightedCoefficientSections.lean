module
public import Linear.NativeProjectiveWeightedChartCoefficient
public import Linear.ModuleBaseSourceLocalizationNaturality
public import Linear.NativeBaseSourceSectionsOverlap
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
/-- The ACTUAL original weighted base-to-source section map commutes with
an ORIGINAL S-linear coefficient map and its ORIGINAL R restriction. -/
theorem nativeBaseSourceWeightedChartSection_coefficient (d : ℕ) (a : R) (ha : a ∈ A d)
    (x : nativeGradedModuleAwayDegreeZero A D d a) :
    nativeProjectiveDegreeZeroSectionMap B D E hSD hSE f hf 0
      (op (Proj.basicOpen B (algebraMap R S a)))
      (nativeBaseSourceWeightedChartSection A B D (hR:=hRD) (hS:=hSD) d a ha x) =
      nativeBaseSourceWeightedChartSection A B E (hR:=hRE) (hS:=hSE) d a ha
        (nativeGradedModuleAwayDegreeZeroCoefficientMap A D E hRD (f.restrictScalars R) hf d a ha x) := by
  apply Subtype.ext
  funext p
  change nativeProjectiveModuleAtPrimeMap B f p.1
    (nativeProjectiveChartRefinement B (algebraMap R S a)
      (moduleBaseSourceLocalizationEquiv (S:=S) a x.val) p) =
    nativeProjectiveChartRefinement B (algebraMap R S a)
      (moduleBaseSourceLocalizationEquiv (S:=S) a
        (LocalizedModule.map (Submonoid.powers a) (f.restrictScalars R) x.val)) p
  exact (nativeProjectiveChartRefinement_coefficient B (algebraMap R S a) f
    (moduleBaseSourceLocalizationEquiv (S:=S) a x.val) p).trans
    (congrArg (fun z => nativeProjectiveChartRefinement B (algebraMap R S a) z p)
      (moduleBaseSourceLocalizationEquiv_map a f x.val))
end LinearStudy
