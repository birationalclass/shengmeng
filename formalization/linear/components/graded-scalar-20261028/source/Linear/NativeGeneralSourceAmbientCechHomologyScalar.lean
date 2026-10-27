module
public import Linear.NativeGeneralSourceAmbientOrderedTwistCech
public import Linear.NativeGeneralSourceAmbientOrderedTwistCechScalar
public import Linear.NativeGeneralNormalizationCachedCechComparison
public import Linear.OrderedCechModuleScalarNaturality
public import Linear.NativeProjectiveTwistRegrading
public import Linear.NativeFiniteGradedSourceAmbientOrderedTwistCech
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
open CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
variable [LinearOrder ι]
attribute [local irreducible] nativeProjectiveModuleSheaf nativeProjectiveModulePresheaf
  schemeModuleToActualAbelianSheaf nativeIndependentSourceAmbientOrderedCechIso_general
  orderedFormalCechComplex FormalCoproduct.evalOp orderedTopAbelianCechComplex
  orderedTopAbelianCechCoefficientMap orderedTopAbelianCechCoefficientIso nativeProjectiveTwistRegradingIso
attribute [local irreducible] nativeIndependentSourceAmbientOrderedTwistCechIso_general
/-- The SAME original all-twist Cech homology comparison commutes with
ORIGINAL base-global coefficient scalars in every positive degree. -/
theorem nativeIndependentFiniteNormalization_cachedCechHomologyIso_baseScalar_general
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (k : ℤ) (q : ℕ)
    (r : Γ(Spec (CommRingCat.of K),⊤)) :
    let fA := (schemeModuleToActualAbelianSheaf (Proj A)).map
      (originalGlobalModuleScalar
        ((Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom (algebraMap K (A 0)))).appTop r)
        (nativeProjectiveModuleSheaf A D hR k))
    let fB := (schemeModuleToActualAbelianSheaf (Proj B)).map
      (originalGlobalModuleScalar
        ((Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))).appTop r)
        (nativeProjectiveModuleSheaf B D hS k))
    HomologicalComplex.homologyMap
      (orderedTopAbelianCechCoefficientMap (Proj A) (fun i => Proj.basicOpen A (a i)) fA) (q+1) ≫
      (nativeIndependentFiniteNormalization_cachedCechHomologyIso_general A B D hR hS a ha c hc hgenR hgenC k q).hom =
    (nativeIndependentFiniteNormalization_cachedCechHomologyIso_general A B D hR hS a ha c hc hgenR hgenC k q).hom ≫
      HomologicalComplex.homologyMap
        (orderedTopAbelianCechCoefficientMap (Proj B) (fun i => Proj.basicOpen B (algebraMap R S (a i))) fB) (q+1) := by
  let T := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) (q+1)
  exact (T.map_commSq (show CommSq _ _ _ _ from
    ⟨(nativeIndependentSourceAmbientOrderedTwistCechIso_baseScalar_general A B D hR hS a ha c hc
      hgenR hgenC k r).symm⟩)).w
end LinearStudy
