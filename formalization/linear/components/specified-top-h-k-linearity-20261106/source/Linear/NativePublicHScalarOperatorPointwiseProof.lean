module
public import Linear.NativeSourceActualHCachedComparison
public import Linear.NativeProjectiveOriginalHScalarObjects
public import Linear.NativePublicHScalarOperatorIdentity
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
/-- Pointwise identity between the public typed ORIGINAL scalar map
and its literal original coefficient-H operator. -/
def nativeOriginalActualHPublicScalarOperator_apply_eq_raw_proof
    (hcover : (⨆ i,Proj.basicOpen B (b i)) = ⊤) (k : ℤ) (q : ℕ)
    (r : Γ(Spec (CommRingCat.of K),⊤))
    (y : schemeModuleActualHObject (Proj B) (nativeProjectiveModuleSheaf B D hD k) (q+1)) :=
  ConcreteCategory.congr_hom
    (X := schemeModuleActualHObject (Proj B) (nativeProjectiveModuleSheaf B D hD k) (q+1))
    (Y := schemeModuleActualHObject (Proj B) (nativeProjectiveModuleSheaf B D hD k) (q+1))
    (nativeOriginalActualHPublicScalarOperator_eq_raw B D hD b hb hcover k q r) y
end LinearStudy
#check LinearStudy.nativeOriginalActualHPublicScalarOperator_apply_eq_raw_proof
#print axioms LinearStudy.nativeOriginalActualHPublicScalarOperator_apply_eq_raw_proof
