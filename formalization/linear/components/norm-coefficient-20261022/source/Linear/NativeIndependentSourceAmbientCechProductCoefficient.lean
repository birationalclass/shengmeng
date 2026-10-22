module
public import Linear.NativeIndependentSourceAmbientCoefficientSections
public import Linear.NativeIndependentSourceAmbientCechObjects
public import Linear.ConcreteAdditiveEquivNaturality
public import Linear.NativeProjectiveDegreeZeroActualCoefficientValue
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
variable [DirectSum.Decomposition D] [DirectSum.Decomposition E]
variable [IsScalarTower K R M] [IsScalarTower K S M]
variable [IsScalarTower K R N] [IsScalarTower K S N]
variable [IsDomain S] [Module.IsTorsionFree S M] [Module.IsTorsionFree S N]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [Module.Finite R M] [Module.Finite S M] [Module.Finite R N] [Module.Finite S N]
variable {ι κ : Type u} (a : ι → R) (ha : ∀ i,a i ∈ A 1)
variable (c : κ → S) (hc : ∀ i,c i ∈ B 1)
attribute [local irreducible] nativeWeightedSourceAmbientSectionAddEquiv
attribute [local irreducible] nativeIndependentSourceAmbientCechSectionAddEquiv
/-- The SAME product-chart comparison is natural for the ORIGINAL actual
abelian-sheaf coefficient map between TWO finite graded modules. Every local
bijection is derived;source coordinates c generate S independently of a. -/
theorem nativeIndependentSourceAmbientCechProductIso_coefficient
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (p : ℕ) (t : Fin (p+1) → ι) :
    let fA := ((schemeModuleToActualAbelianSheaf (Proj A)).map
      (nativeProjectiveDegreeZeroSheafMap A D E hRD hRE (f.restrictScalars R) hf 0)).hom
    let fB := ((schemeModuleToActualAbelianSheaf (Proj B)).map
      (nativeProjectiveDegreeZeroSheafMap B D E hSD hSE f hf 0)).hom
    (nativeIndependentSourceAmbientCechProductIso A B D hRD hSD a ha c hc hgenR hgenC p t).hom ≫
      fB.app (op (Proj.basicOpen B (algebraMap R S (∏ j : Fin (p+1),a (t j))))) =
    fA.app (op (Proj.basicOpen A (∏ j : Fin (p+1),a (t j)))) ≫
      (nativeIndependentSourceAmbientCechProductIso A B E hRE hSE a ha c hc hgenR hgenC p t).hom := by
  let fA := ((schemeModuleToActualAbelianSheaf (Proj A)).map
    (nativeProjectiveDegreeZeroSheafMap A D E hRD hRE (f.restrictScalars R) hf 0)).hom
  let fB := ((schemeModuleToActualAbelianSheaf (Proj B)).map
    (nativeProjectiveDegreeZeroSheafMap B D E hSD hSE f hf 0)).hom
  let UA := Proj.basicOpen A (∏ j : Fin (p+1),a (t j))
  let UB := Proj.basicOpen B (algebraMap R S (∏ j : Fin (p+1),a (t j)))
  let eD := nativeIndependentSourceAmbientCechSectionAddEquiv A B D hRD hSD a ha c hc hgenR hgenC p t
  let eE := nativeIndependentSourceAmbientCechSectionAddEquiv A B E hRE hSE a ha c hc hgenR hgenC p t
  apply additiveEquivIso_coefficient eD eE (fA.app (op UA)) (fB.app (op UB))
  intro x
  change eE (nativeProjectiveDegreeZeroSectionMap A D E hRD hRE
    (f.restrictScalars R) hf 0 (op UA) x) =
      nativeProjectiveDegreeZeroSectionMap B D E hSD hSE f hf 0 (op UB) (eD x)
  exact nativeIndependentSourceAmbientCechSectionAddEquiv_coefficient A B D E hRD hSD hRE hSE f hf
    a ha c hc hgenR hgenC p t x
end LinearStudy
