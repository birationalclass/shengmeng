module
public import Linear.NativeCechProductChartFaces
public import Linear.OrderedCrossSpaceProductChartComplexIso
public import Linear.NativeGeneralSourceAmbientCechProductFamily
public import Linear.OrderedCrossSpaceAbelianCechIso
public import Linear.OrderedFreeSheafHomComplex
/- Arbitrary finite coefficients;the original fraction maps,ordered signs and actual-H objects are retained.Normalized dualizing trace remains OPEN. -/
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
attribute [local irreducible] orderedCrossSpaceAbelianCechComplexIso_of_productCharts
  orderedCrossSpaceAbelianCechComplexIso
  nativeIndependentSourceAmbientCechProductFamily_general
  nativeIndependentSourceAmbientCechProductIso_general
  nativeProjectiveModuleSheaf nativeProjectiveModulePresheaf
  schemeModuleToActualAbelianSheaf
set_option diagnostics true
set_option diagnostics.threshold 10
/-- Partial application of the actual original Cech constructor. Its remaining
face-proof argument is discharged in the final construction,not assumed. -/
def nativeIndependentSourceAmbientOrderedCechBuilder_general
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) :=
  let F := ((schemeModuleToActualAbelianSheaf (Proj A)).obj (nativeProjectiveModuleSheaf A D hR 0)).obj
  let G := ((schemeModuleToActualAbelianSheaf (Proj B)).obj (nativeProjectiveModuleSheaf B D hS 0)).obj
  let U := fun i => Proj.basicOpen A (a i)
  let V := fun i => Proj.basicOpen B (algebraMap R S (a i))
  let P := nativeCechProductOpen A a
  let Q := nativeBaseSourceCechProductOpen B a
  let rP := nativeCechProductFace A a
  let rQ := nativeBaseSourceCechProductFace B a
  orderedCrossSpaceAbelianCechComplexIso_of_productCharts F G U V P Q
    (fun p t => nativeProjective_cechIntersection_eq_basicOpen A a p t.1)
    (fun p t => nativeSourceCoordinateCechIntersection_eq_basicOpen B a p t.1)
    rP rQ
    (nativeIndependentSourceAmbientCechProductFamily_general A B D hR hS a ha c hc hgenR hgenC)
end LinearStudy
