module
public import Linear.NativeNormalizationActualHCachedComparison
public import Linear.NativeNormalizationCachedCechComparison
public import Linear.NativeSourceActualHCachedComparison
public import Linear.NativeIndependentNormalizationActualHFactorization
public import Linear.NativeProjectiveCechHomologyObjects
public import Linear.SchemeModuleActualHObjects
public import Linear.FiniteNormalizationCoordinateCover
public import Linear.NativeProjActualHComparison
public import Linear.NativeProjectiveTwistFinitePresentation
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
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (B : ℕ → Submodule K S) [GradedAlgebra B] [SetLike.GradedSMul A B]
variable [AddCommGroup M] [Module K M] [Module R M] [Module S M]
variable [IsScalarTower R S M] [IsScalarTower K R M] [IsScalarTower K S M]
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hR : ∀ n : ℕ,∀ j : ℤ,∀ z : R,z ∈ A n → ∀ x : M,x ∈ D j → z • x ∈ D ((n : ℤ)+j))
variable (hS : ∀ n : ℕ,∀ j : ℤ,∀ z : S,z ∈ B n → ∀ x : M,x ∈ D j → z • x ∈ D ((n : ℤ)+j))
variable [IsDomain S] [Module.IsTorsionFree S M]
variable [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.FiniteType K S]
variable [Module.Finite R S] [Module.Finite R M] [Module.Finite S M]
variable {ι κ : Type u} [LinearOrder ι] [Finite ι]
variable (a : ι → R) (ha : ∀ i,a i ∈ A 1)
variable (c : κ → S) (hc : ∀ i,c i ∈ B 1)
/-- EXACT factorization of the SAME original normalization map through
its original Cech and source-H factors,with named exact objects. -/
theorem nativeIndependentFiniteNormalization_cachedActualHigherHIso_factorization
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (k : ℤ) (q : ℕ) :
    nativeIndependentFiniteNormalization_cachedActualHigherHIso A B D hR hS a ha c hc hgenR hgenC k q =
      nativeIndependentFiniteNormalization_cachedCechHomologyIso A B D hR hS a ha c hc hgenR hgenC k q ≪≫
      nativeFiniteGradedTwist_cachedActualHigherHIso B D hS
        (fun i => algebraMap R S (a i))
        (fun i => (normalizationBaseGradedRingHom A B).map_mem (ha i))
        (nativeFiniteNormalization_sourceCoordinateCover A B a ha hgenR) k q := by
  letI : (nativeProjectiveModuleSheaf B D hS k).IsQuasicoherent :=
    nativeFiniteGradedTwist_isQuasicoherent_of_cover B D hS k c hc
      (degreeOneGenerated_nativeProj_cover B c hc hgenC)
  exact nativeIndependentFiniteNormalization_actualHigherHIso_factorization A B D hR hS a ha c hc
    hgenR hgenC k q
end LinearStudy
