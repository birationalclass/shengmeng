module
public import Linear.NativeGeneralPublicHFactorizationCompositeHom
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
/-- Full ORIGINAL scalar square for the SAME PUBLIC general comparison.
All hypotheses are those of the original arbitrary finite graded comparison. -/
def nativeIndependentFiniteNormalization_publicActualHigherHIso_baseScalar_explicit_proof
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (k : ℤ) (q : ℕ)
    (r : Γ(Spec (CommRingCat.of K),⊤)) :=
  let b := fun i => algebraMap R S (a i)
  let hb := fun i => (normalizationBaseGradedRingHom A B).map_mem (ha i)
  let hcover := nativeFiniteNormalization_sourceCoordinateCover A B a ha hgenR
  originalEndomorphismSquare_of_comparison_eq (C := AddCommGrpCat.{u})
    (X := nativeProjectiveOrderedCechHomologyObject A D hR a k (q+1))
    (Y := schemeModuleActualHObject (Proj B) (nativeProjectiveModuleSheaf B D hS k) (q+1))
    (a := HomologicalComplex.homologyMap
      (orderedTopAbelianCechCoefficientMap (Proj A) (fun i => Proj.basicOpen A (a i))
        ((schemeModuleToActualAbelianSheaf (Proj A)).map
          (originalGlobalModuleScalar
            ((Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom (algebraMap K (A 0)))).appTop r)
            (nativeProjectiveModuleSheaf A D hR k)))) (q+1))
    (d := nativeOriginalActualHPublicScalarOperator B D hS b hb hcover k q r)
    (j := (nativeIndependentFiniteNormalization_actualHigherHIso_general A B D hR hS a ha c hc hgenR hgenC k q).hom)
    (j0 := (nativeIndependentFiniteNormalization_cachedCechHomologyIso_general A B D hR hS a ha c hc hgenR hgenC k q).hom ≫
      (nativeFiniteGradedTwist_cachedActualHigherHIso B D hS b hb hcover k q).hom)
    (nativeIndependentFiniteNormalization_publicActualHHom_factorization_composite_proof A B D hR hS a ha c hc hgenR hgenC k q)
    (nativeIndependentFiniteNormalization_publicActualHComposite_baseScalar_general A B D hR hS a ha c hc hgenR hgenC k q r)
end LinearStudy
#check LinearStudy.nativeIndependentFiniteNormalization_publicActualHigherHIso_baseScalar_explicit_proof
#print axioms LinearStudy.nativeIndependentFiniteNormalization_publicActualHigherHIso_baseScalar_explicit_proof
