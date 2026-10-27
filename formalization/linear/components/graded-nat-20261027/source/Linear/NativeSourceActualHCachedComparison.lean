module
public import Linear.NativeFiniteGradedSourceActualHCoefficient
public import Linear.NativeProjectiveCechHomologyObjects
public import Linear.SchemeModuleActualHObjects
public import Linear.NativeProjectiveTwistQuasicoherent
public import Linear.NativeProjectiveDegreeZeroMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K S M N : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable [AddCommGroup N] [Module K N] [Module S N] [IsScalarTower K S N]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (D : ℤ → Submodule K M) (E : ℤ → Submodule K N)
variable [DirectSum.Decomposition D] [DirectSum.Decomposition E]
variable (hD : ∀ n : ℕ,∀ j : ℤ,∀ z : S,z ∈ B n → ∀ x : M,x ∈ D j → z • x ∈ D ((n:ℤ)+j))
variable (hE : ∀ n : ℕ,∀ j : ℤ,∀ z : S,z ∈ B n → ∀ x : N,x ∈ E j → z • x ∈ E ((n:ℤ)+j))
variable (f : M →ₗ[S] N) (hf : ∀ j : ℤ,∀ x : M,x ∈ D j → f x ∈ E j)
variable [IsNoetherianRing S] [Algebra.FiniteType K S] [Module.Finite S M] [Module.Finite S N]
variable {ι : Type u} [LinearOrder ι] [Finite ι] (b : ι → S) (hb : ∀ i,b i ∈ B 1)
attribute [local irreducible] finiteTypeNativeProj_orderedActualHigherHIso
  noetherianFiniteOrderedAffineCover_actualHigherHIso topFiniteOrderedCech_actualHigherHIso_of_localAcyclic
  orderedFreeSheafActualHomComplexIso acyclicResolutionActualCochainExtIso
/-- The SAME actual source ordered-Cech/native-H comparison,with exact
named objects. Original source QC is DERIVED from its degree-one cover. -/
def nativeFiniteGradedTwist_cachedActualHigherHIso
    (hcover : (⨆ i,Proj.basicOpen B (b i)) = ⊤) (k : ℤ) (q : ℕ) :
    nativeProjectiveOrderedCechHomologyObject B D hD b k (q+1) ≅
      schemeModuleActualHObject (Proj B) (nativeProjectiveModuleSheaf B D hD k) (q+1) := by
  letI : (nativeProjectiveModuleSheaf B D hD k).IsQuasicoherent :=
    nativeFiniteGradedTwist_isQuasicoherent_of_cover B D hD k b hb hcover
  exact finiteTypeNativeProj_orderedActualHigherHIso B b hb hcover (nativeProjectiveModuleSheaf B D hD k) q
/-- Exact original coefficient naturality of this SAME source comparison,
all integer twists and positive degrees. BOTH native QC facts are derived. -/
theorem nativeFiniteGradedTwist_cachedActualHigherHIso_coefficient
    (hcover : (⨆ i,Proj.basicOpen B (b i)) = ⊤) (k : ℤ) (q : ℕ) :
    nativeProjectiveOrderedCechHomologyCoefficientHom B D E hD hE f hf b k (q+1) ≫
      (nativeFiniteGradedTwist_cachedActualHigherHIso B E hE b hb hcover k q).hom =
    (nativeFiniteGradedTwist_cachedActualHigherHIso B D hD b hb hcover k q).hom ≫
      schemeModuleActualHCoefficientHom (nativeProjectiveDegreeZeroSheafMap B D E hD hE f hf k) (q+1) := by
  letI : (nativeProjectiveModuleSheaf B D hD k).IsQuasicoherent :=
    nativeFiniteGradedTwist_isQuasicoherent_of_cover B D hD k b hb hcover
  letI : (nativeProjectiveModuleSheaf B E hE k).IsQuasicoherent :=
    nativeFiniteGradedTwist_isQuasicoherent_of_cover B E hE k b hb hcover
  exact nativeFiniteGradedTwist_actualHigherHIso_coefficient B D E hD hE f hf b hb hcover k q
end LinearStudy
