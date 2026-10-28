module
public import Linear.NativeGeneralNormalizationModuleHFactorization
public import Linear.NativeGeneralPublicHScalarTheorem
public import Linear.NativeProjectiveModuleCechHomologyObjects
public import Linear.OrderedModuleCechActualAbelianHomology
public import Linear.CategoricalOriginalSquareRefold
public import Linear.NativeGeneralPublicHScalarCompositeTheorem
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
open AlgebraicGeometry.Scheme.Modules
/-- Compose original module-homology forgetting scalar naturality with
the proved SAME public general actual-H scalar square. -/
def nativeFiniteNormalization_generalModuleCechActualHComposite_baseScalar_proof
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (k : ℤ) (q : ℕ)
    (r : Γ(Spec (CommRingCat.of K),⊤)) :=
  let piA := Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom (algebraMap K (A 0)))
  let MA := nativeProjectiveModuleSheaf A D hR k
  originalEndomorphismSquare_comp (C := AddCommGrpCat.{u})
    (A := nativeProjectiveOrderedModuleCechHomologyObject A D hR piA a k (q+1))
    (B := nativeProjectiveOrderedCechHomologyObject A D hR a k (q+1))
    (D := schemeModuleActualHObject (Proj B) (nativeProjectiveModuleSheaf B D hS k) (q+1))
    (orderedModuleCechActualAbelianHomologyIso_coefficient_naturality piA
      (originalGlobalModuleScalar (piA.appTop r) MA) (fun i => Proj.basicOpen A (a i)) (q+1))
    (nativeIndependentFiniteNormalization_publicActualHigherHIso_baseScalar_general A B D hR hS a ha c hc hgenR hgenC k q r)
end LinearStudy
#check LinearStudy.nativeFiniteNormalization_generalModuleCechActualHComposite_baseScalar_proof
#print axioms LinearStudy.nativeFiniteNormalization_generalModuleCechActualHComposite_baseScalar_proof
