module
public import Linear.NativeWeightedSourceAmbientSectionEquiv
public import Linear.NativeWeightedSourceAmbientSectionScalar
public import Linear.ProjBasicOpenBaseScalar
public import Linear.ProjBasicOpenNormalizationBaseScalar
public import Linear.OriginalScalarComparisonCalibration
public import Linear.NativeProjectiveModuleScalarApply
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 5000
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
attribute [local irreducible] nativeProjectiveModuleSections nativeProjectiveModulePresheaf nativeProjectiveModuleSheaf
/-- The original base-global-section scalar square on a weighted product chart.
The two chart bijections are explicit LOCAL inputs here,not global linearity. -/
def nativeWeightedSourceAmbientSectionAddEquiv_originalBaseScalar_proof
    (d : ℕ) (a : R) (ha : a ∈ A d) (hd : 0<d)
    (hA : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap A D hR d a ha))
    (hB : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap B D hS d
      (algebraMap R S a) ((normalizationBaseGradedRingHom A B).map_mem ha)))
    (r : Γ(Spec (CommRingCat.of K),⊤))
    (s : nativeProjectiveModuleSections A D hR 0 (op (Proj.basicOpen A a))) :=
  let scalar := (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r
  let z := HomogeneousLocalization.fromZeroRingHom A (Submonoid.powers a) (algebraMap K (A 0) scalar)
  let e := nativeWeightedSourceAmbientSectionAddEquiv A B D hR hS d a ha hA hB
  let alpha := nativeProjectiveModuleScalarApply A D hR 0 (op (Proj.basicOpen A a))
  let beta := nativeProjectiveModuleScalarApply B D hS 0 (op (Proj.basicOpen B (algebraMap R S a)))
  let h0 := nativeWeightedSourceAmbientSectionAddEquiv_smul A B D hR hS d a ha hA hB z s
  originalScalarComparison_of_calibrations e alpha beta (Proj.awayToSection A a).hom
    ((Proj.awayToSection B (algebraMap R S a)).hom.comp (normalizationHomogeneousChartMap A B a)) z
    (projBasicOpenBaseScalar A (algebraMap K (A 0)) a r)
    (projBasicOpenBaseScalar B (algebraMap K (B 0)) (algebraMap R S a) r) s
    (projBasicOpenBaseScalar_eq_chart A (algebraMap K (A 0)) a ha hd r)
    (projBasicOpenBaseScalar_eq_normalizationChart A B a ha hd r) h0
end LinearStudy
