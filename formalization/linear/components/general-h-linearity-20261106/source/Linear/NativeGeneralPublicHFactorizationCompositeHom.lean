module
public import Linear.NativeGeneralNormalizationActualHFactorization
public import Linear.NativeSourcePublicHComparisonTypedHom
public import Linear.CategoricalIsoTransHomEquality
public import Linear.SchemeModuleActualCohomologyGroup
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
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (B : ℕ → Submodule K S) [GradedAlgebra B] [SetLike.GradedSMul A B]
variable [AddCommGroup M] [Module K M] [Module R M] [Module S M]
variable [IsScalarTower R S M] [IsScalarTower K R M] [IsScalarTower K S M]
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hR : ∀ n : ℕ,∀ j : ℤ,∀ z : R,z ∈ A n → ∀ x : M,x ∈ D j → z • x ∈ D ((n : ℤ)+j))
variable (hS : ∀ n : ℕ,∀ j : ℤ,∀ z : S,z ∈ B n → ∀ x : M,x ∈ D j → z • x ∈ D ((n : ℤ)+j))
variable [IsDomain R] [IsDomain S]
variable [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.FiniteType K S]
variable [Module.Finite R S] [Module.Finite R M] [Module.Finite S M]
variable {ι κ : Type u} [LinearOrder ι] [Finite ι]
variable (a : ι → R) (ha : ∀ i,a i ∈ A 1)
variable (c : κ → S) (hc : ∀ i,c i ∈ B 1)
attribute [local irreducible] nativeProjectiveModuleSheaf schemeModuleToActualAbelianSheaf
  nativeIndependentSourceAmbientOrderedTwistCechIso_general
attribute [local instance] schemeModuleActualCohomologyAddCommGroup
attribute [local irreducible] nativeIndependentFiniteNormalization_actualHigherHIso_general
  nativeIndependentFiniteNormalization_cachedCechHomologyIso_general
  nativeFiniteGradedTwist_cachedActualHigherHIso
  nativeProjectiveOrderedCechHomologyObject schemeModuleActualHObject
/-- The underlying Hom equality of the already proved SAME public factorization. -/
def nativeIndependentFiniteNormalization_publicActualHHom_factorization_composite_proof
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (k : ℤ) (q : ℕ) :=
  originalIsoTransHom_of_eq (C := AddCommGrpCat.{u})
    (X := nativeProjectiveOrderedCechHomologyObject A D hR a k (q+1))
    (Y := nativeProjectiveOrderedCechHomologyObject B D hS (fun i => algebraMap R S (a i)) k (q+1))
    (Z := schemeModuleActualHObject (Proj B) (nativeProjectiveModuleSheaf B D hS k) (q+1))
    (nativeIndependentFiniteNormalization_actualHigherHIso_factorization_general A B D hR hS a ha c hc hgenR hgenC k q)
end LinearStudy
#check LinearStudy.nativeIndependentFiniteNormalization_publicActualHHom_factorization_composite_proof
#print axioms LinearStudy.nativeIndependentFiniteNormalization_publicActualHHom_factorization_composite_proof
