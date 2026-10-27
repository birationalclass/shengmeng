module
public import Linear.NativeSourceActualHCachedComparison
public import Linear.NativeProjectiveOriginalHScalarObjects
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hD : ∀ n : ℕ,∀ j : ℤ,∀ z : S,z ∈ B n → ∀ x : M,x ∈ D j → z • x ∈ D ((n:ℤ)+j))
variable [IsNoetherianRing S] [Algebra.FiniteType K S] [Module.Finite S M]
variable {ι : Type u} [LinearOrder ι] [Finite ι] (b : ι → S) (hb : ∀ i,b i ∈ B 1)
attribute [local irreducible] nativeProjectiveModuleSheaf nativeProjectiveModulePresheaf
  schemeModuleToActualAbelianSheaf originalGlobalModuleScalar
  finiteTypeNativeProj_orderedActualHigherHIso noetherianFiniteOrderedAffineCover_actualHigherHIso
  topFiniteOrderedCech_actualHigherHIso_of_localAcyclic orderedFreeSheafActualHomComplexIso
  acyclicResolutionActualCochainExtIso orderedTopAbelianCechCoefficientMap orderedTopAbelianCechComplex
/-- Derived actual source-H scalar naturality before folding the SAME cached comparison name. -/
def nativeFiniteGradedTwist_actualHigherHIso_baseScalar_proof
    (hcover : (⨆ i,Proj.basicOpen B (b i)) = ⊤) (k : ℤ) (q : ℕ)
    (r : Γ(Spec (CommRingCat.of K),⊤)) :=
  letI := nativeFiniteGradedTwist_isQuasicoherent_of_cover B D hD k b hb hcover
  finiteTypeNativeProj_orderedActualHigherHIso_coefficient_naturality B b hb hcover
    (originalGlobalModuleScalar
      ((Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))).appTop r)
      (nativeProjectiveModuleSheaf B D hD k)) q
end LinearStudy
