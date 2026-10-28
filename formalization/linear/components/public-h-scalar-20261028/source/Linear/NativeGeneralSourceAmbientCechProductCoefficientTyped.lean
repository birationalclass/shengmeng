module
public import Linear.NativeGeneralSourceAmbientCechProductCoefficient
public import Linear.NativeGeneralSourceAmbientCechObjects
public import Linear.ConcreteAdditiveEquivNaturality
public import Linear.NativeProjectiveDegreeZeroActualCoefficientValue
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 5000
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
variable [DirectSum.Decomposition D] [DirectSum.Decomposition E]
variable [IsScalarTower K R M] [IsScalarTower K S M]
variable [IsScalarTower K R N] [IsScalarTower K S N]
variable [IsDomain R] [IsDomain S]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [Module.Finite R M] [Module.Finite S M] [Module.Finite R N] [Module.Finite S N]
variable {ι κ : Type u} (a : ι → R) (ha : ∀ i,a i ∈ A 1)
variable (c : κ → S) (hc : ∀ i,c i ∈ B 1)
attribute [local irreducible] nativeWeightedSourceAmbientSectionAddEquiv
attribute [local irreducible] nativeIndependentSourceAmbientCechSectionAddEquiv_general
  nativeProjectiveModuleSheaf nativeProjectiveModulePresheaf schemeModuleToActualAbelianSheaf
/-- The SAME product-chart comparison is natural for the ORIGINAL actual
abelian-sheaf coefficient map between TWO finite graded modules. Every local
bijection is derived;source coordinates c generate S independently of a. -/
theorem nativeIndependentSourceAmbientCechProductIso_coefficient_general_typed
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (p : ℕ) (t : Fin (p+1) → ι) :
    let fA := ((schemeModuleToActualAbelianSheaf (Proj A)).map
      (nativeProjectiveDegreeZeroSheafMap A D E hRD hRE (f.restrictScalars R) hf 0)).hom
    let fB := ((schemeModuleToActualAbelianSheaf (Proj B)).map
      (nativeProjectiveDegreeZeroSheafMap B D E hSD hSE f hf 0)).hom
    (nativeIndependentSourceAmbientCechProductIso_general A B D hRD hSD a ha c hc hgenR hgenC p t).hom ≫
      fB.app (op (Proj.basicOpen B (algebraMap R S (∏ j : Fin (p+1),a (t j))))) =
    fA.app (op (Proj.basicOpen A (∏ j : Fin (p+1),a (t j)))) ≫
      (nativeIndependentSourceAmbientCechProductIso_general A B E hRE hSE a ha c hc hgenR hgenC p t).hom :=
  nativeIndependentSourceAmbientCechProductIso_coefficient_general A B D E hRD hSD hRE hSE f hf
    a ha c hc hgenR hgenC p t
end LinearStudy
