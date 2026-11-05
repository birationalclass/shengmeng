module
public import Linear.NativeGeneralSourceAmbientOriginalBaseScalar
public import Linear.ProjBasicOpenBaseScalar
public import Linear.NativeProjectiveModuleScalarApply
public import Linear.NormalizationChartConstants
public import Linear.NativeWeightedSourceAmbientSectionScalar
public import Linear.NativeFiniteGradedIndependentCechSections
public import Linear.NativeFiniteGradedWeightedSectionsFunctionSurjective
public import Linear.NativeBaseSourceBaseChartInjective
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 5000
set_option diagnostics true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K R S M : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable [AddCommGroup M] [Module K M] [Module R M] [Module S M]
variable [IsScalarTower R S M] [IsScalarTower K R M] [IsScalarTower K S M]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (B : ℕ → Submodule K S) [GradedAlgebra B] [SetLike.GradedSMul A B]
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hR : ∀ n : ℕ,∀ j : ℤ,∀ c : R,c ∈ A n → ∀ x : M,x ∈ D j → c • x ∈ D ((n : ℤ)+j))
variable (hS : ∀ n : ℕ,∀ j : ℤ,∀ c : S,c ∈ B n → ∀ x : M,x ∈ D j → c • x ∈ D ((n : ℤ)+j))
variable [IsDomain R] [IsDomain S]
variable [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite R M] [Module.Finite S M]
variable {ι : Type u} (a : ι → R) (ha : ∀ i,a i ∈ A 1)
variable {κ : Type u} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
include c hc
attribute [local instance] nativeHomogeneousAwayModuleScalar LocalizedModule.moduleOfIsLocalization
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
attribute [local irreducible] projBasicOpenBaseScalar
/-- The SAME actual finite-normalization section comparison commutes
with the ORIGINAL base-global-section actions obtained from the two Proj
structure maps to Spec K. Both chart bijections and scalar calibration
are derived; no H-linearity premise is assumed. -/
theorem nativeIndependentSourceAmbientCechSectionAddEquiv_baseScalar_general_typed
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (p : ℕ) (t : Fin (p+1) → ι)
    (r : Γ(Spec (CommRingCat.of K),⊤))
    (s : nativeProjectiveModuleSections A D hR 0
      (op (Proj.basicOpen A (∏ j : Fin (p+1),a (t j))))) :
    nativeIndependentSourceAmbientCechSectionAddEquiv_general A B D hR hS a ha c hc
      hgenR hgenC p t
      (nativeProjectiveModuleScalarApply A D hR 0
        (op (Proj.basicOpen A (∏ j : Fin (p+1),a (t j))))
        (projBasicOpenBaseScalar A (algebraMap K (A 0)) (∏ j : Fin (p+1),a (t j)) r) s) =
    nativeProjectiveModuleScalarApply B D hS 0
      (op (Proj.basicOpen B (algebraMap R S (∏ j : Fin (p+1),a (t j)))))
      (projBasicOpenBaseScalar B (algebraMap K (B 0)) (algebraMap R S (∏ j : Fin (p+1),a (t j))) r)
      (nativeIndependentSourceAmbientCechSectionAddEquiv_general A B D hR hS a ha c hc
        hgenR hgenC p t s) := by
  simpa only [nativeIndependentSourceAmbientCechSectionAddEquiv_general] using
    (nativeIndependentSourceAmbientCechSectionAddEquiv_originalBaseScalar_general_proof
      A B D hR hS a ha c hc hgenR hgenC p t r s)
end LinearStudy
