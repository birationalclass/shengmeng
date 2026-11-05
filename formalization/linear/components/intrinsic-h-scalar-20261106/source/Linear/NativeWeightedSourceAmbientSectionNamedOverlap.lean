module
public import Linear.NativeWeightedSourceAmbientSectionEquiv
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
attribute [local irreducible] nativeWeightedSourceAmbientSectionAddEquiv
/-- The actual weighted restriction square also retains any specified product
name c.This transports the proof together with its homogeneous degree data. -/
theorem nativeWeightedSourceAmbientSectionAddEquiv_overlap_named
    (d e : ℕ) (a b c : R) (ha : a ∈ A d) (hb : b ∈ A e)
    (hc : c ∈ A (d+e)) (hprod : c=a*b)
    (hA : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap A D hR d a ha))
    (hB : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap B D hS d
      (algebraMap R S a) ((normalizationBaseGradedRingHom A B).map_mem ha)))
    (hC : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap A D hR (d+e) c hc))
    (hD : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap B D hS (d+e)
      (algebraMap R S c) ((normalizationBaseGradedRingHom A B).map_mem hc)))
    (s : nativeProjectiveModuleSections A D hR 0 (op (Proj.basicOpen A a))) :
    nativeWeightedSourceAmbientSectionAddEquiv A B D hR hS (d+e) c hc hC hD
      ((nativeProjectiveModulePresheaf A D hR 0).map
        (homOfLE (show Proj.basicOpen A c ≤ Proj.basicOpen A a from by
          rw [hprod];exact ProjectiveSpectrum.basicOpen_mul_le_left A a b)).op s) =
      (nativeProjectiveModulePresheaf B D hS 0).map
        (homOfLE (show Proj.basicOpen B (algebraMap R S c) ≤
          Proj.basicOpen B (algebraMap R S a) from by
            rw [hprod,map_mul];exact ProjectiveSpectrum.basicOpen_mul_le_left B _ _)).op
        (nativeWeightedSourceAmbientSectionAddEquiv A B D hR hS d a ha hA hB s) := by
  subst c
  exact nativeWeightedSourceAmbientSectionAddEquiv_overlap A B D hR hS d e a b ha hb hA hB hC hD s
end LinearStudy
