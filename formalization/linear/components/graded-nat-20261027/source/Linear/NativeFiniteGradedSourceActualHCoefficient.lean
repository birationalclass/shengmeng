module
public import Linear.NativeProjActualHCoefficientNaturality
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
/-- The SAME actual source-Cech/native-H comparisons are natural for the
ORIGINAL native degree-zero module-sheaf map,in EVERY integer twist and
positive degree. BOTH original native sheaves are proved quasicoherent
from the given ordinary degree-one COVER;no coefficient square is assumed. -/
theorem nativeFiniteGradedTwist_actualHigherHIso_coefficient
    (hcover : (⨆ i,Proj.basicOpen B (b i)) = ⊤) (k : ℤ) (q : ℕ) :
    let MB := nativeProjectiveModuleSheaf B D hD k
    let NB := nativeProjectiveModuleSheaf B E hE k
    letI : MB.IsQuasicoherent := nativeFiniteGradedTwist_isQuasicoherent_of_cover B D hD k b hb hcover
    letI : NB.IsQuasicoherent := nativeFiniteGradedTwist_isQuasicoherent_of_cover B E hE k b hb hcover
    let fB := nativeProjectiveDegreeZeroSheafMap B D E hD hE f hf k
    HomologicalComplex.homologyMap
      (orderedTopAbelianCechCoefficientMap (Proj B) (fun i => Proj.basicOpen B (b i))
        ((schemeModuleToActualAbelianSheaf (Proj B)).map fB)) (q+1) ≫
      (finiteTypeNativeProj_orderedActualHigherHIso B b hb hcover NB q).hom =
    (finiteTypeNativeProj_orderedActualHigherHIso B b hb hcover MB q).hom ≫
      (CategoryTheory.Sheaf.functorH.{u} (_root_.Opens.grothendieckTopology (Proj B)) (q+1)).map
        ((schemeModuleToActualAbelianSheaf (Proj B)).map fB) := by
  let MB := nativeProjectiveModuleSheaf B D hD k
  let NB := nativeProjectiveModuleSheaf B E hE k
  letI : MB.IsQuasicoherent := nativeFiniteGradedTwist_isQuasicoherent_of_cover B D hD k b hb hcover
  letI : NB.IsQuasicoherent := nativeFiniteGradedTwist_isQuasicoherent_of_cover B E hE k b hb hcover
  exact finiteTypeNativeProj_orderedActualHigherHIso_coefficient_naturality B b hb hcover
    (nativeProjectiveDegreeZeroSheafMap B D E hD hE f hf k) q
end LinearStudy
