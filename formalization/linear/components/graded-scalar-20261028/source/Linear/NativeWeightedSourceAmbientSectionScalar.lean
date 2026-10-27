module
public import Linear.NativeWeightedSourceAmbientSectionEquiv
public import Linear.SemilinearComparisonScalar
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K R S M : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable [AddCommGroup M] [Module K M] [Module R M] [Module S M] [IsScalarTower R S M]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (B : ℕ → Submodule K S) [GradedAlgebra B] [SetLike.GradedSMul A B]
variable (D : ℤ → Submodule K M)
variable (hR : ∀ n : ℕ,∀ j : ℤ,∀ c : R,c ∈ A n → ∀ x : M,x ∈ D j → c • x ∈ D ((n : ℤ)+j))
variable (hS : ∀ n : ℕ,∀ j : ℤ,∀ c : S,c ∈ B n → ∀ x : M,x ∈ D j → c • x ∈ D ((n : ℤ)+j))
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
attribute [local irreducible] nativeProjectiveChartDegreeZeroSectionMap
  nativeBaseSourceWeightedChartSectionLinearMap
/-- The SAME original weighted ambient/source section comparison commutes
with the ACTUAL original homogeneous-chart scalar map. The two LOCAL
section bijections remain explicit here and are derived in finite-data
applications. No desired global H linearity or geometric trace is assumed. -/
theorem nativeWeightedSourceAmbientSectionAddEquiv_smul
    (d : ℕ) (a : R) (ha : a ∈ A d)
    (hA : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap A D hR d a ha))
    (hB : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap B D hS d
      (algebraMap R S a) ((normalizationBaseGradedRingHom A B).map_mem ha)))
    (r : HomogeneousLocalization.Away A a)
    (s : nativeProjectiveModuleSections A D hR 0 (op (Proj.basicOpen A a))) :
    nativeWeightedSourceAmbientSectionAddEquiv A B D hR hS d a ha hA hB
        ((Proj.awayToSection A a).hom r • s) =
      ((Proj.awayToSection B (algebraMap R S a)).hom.comp
        (normalizationHomogeneousChartMap A B a)) r •
          nativeWeightedSourceAmbientSectionAddEquiv A B D hR hS d a ha hA hB s := by
  exact semilinear_bijective_comparison_smul
    (Proj.awayToSection A a).hom
    ((Proj.awayToSection B (algebraMap R S a)).hom.comp
      (normalizationHomogeneousChartMap A B a))
    (nativeProjectiveChartDegreeZeroSectionMap A D hR d a ha)
    (nativeBaseSourceWeightedChartSectionLinearMap A B D hR hS d a ha)
    hA (nativeBaseSourceWeightedChartSectionLinearMap_bijective A B D hR hS d a ha hB)
    r s
end LinearStudy
