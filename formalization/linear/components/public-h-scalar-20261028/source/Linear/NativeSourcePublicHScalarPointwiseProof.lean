module
public import Linear.NativeSourceActualHCachedComparison
public import Linear.NativeProjectiveOriginalHScalarObjects
public import Linear.NativeSourceActualHContextScalarSquare
public import Linear.ConcreteOriginalScalarSquareExt
public import Linear.NativeSourceContextHScalarValueProof
public import Linear.NativeSourcePublicHComparisonPointwiseProof
public import Linear.NativePublicHScalarOperatorPointwiseProof
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
/-- The SAME public source comparison respects the ORIGINAL scalar maps,
proved on their original common carrier from independent map calibrations. -/
def nativeFiniteGradedTwist_publicActualHigherHIso_baseScalar_value_proof
    (hcover : (⨆ i,Proj.basicOpen B (b i)) = ⊤) (k : ℤ) (q : ℕ)
    (r : Γ(Spec (CommRingCat.of K),⊤))
    (x : nativeProjectiveOrderedCechHomologyObject B D hD b k (q+1)) :=
  originalScalarSquare_apply_of_calibrations
    (nativeFiniteGradedTwist_publicActualHHom_apply_eq_original_proof B D hD b hb hcover k q)
    (nativeOriginalActualHPublicScalarOperator_apply_eq_raw_proof B D hD b hb hcover k q r)
    (nativeFiniteGradedTwist_contextActualHigherHIso_baseScalar_value_proof B D hD b hb hcover k q r) x
end LinearStudy
#check LinearStudy.nativeFiniteGradedTwist_publicActualHigherHIso_baseScalar_value_proof
#print axioms LinearStudy.nativeFiniteGradedTwist_publicActualHigherHIso_baseScalar_value_proof
