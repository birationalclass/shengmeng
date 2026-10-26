module
public import Linear.NativeCechProductChartFaces
public import Linear.NativeGeneralSourceAmbientOrderedTwistCech
public import Linear.NativeIndependentSourceAmbientOrderedTwistCech
public import Linear.NativeGeneralSourceAmbientOrderedTwistCech
public import Linear.NativeIndependentSourceAmbientOrderedTwistCech
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
variable [Module.IsTorsionFree S M]
attribute [local irreducible] nativeWeightedSourceAmbientSectionAddEquiv
  nativeProjectiveModuleSheaf schemeModuleToActualAbelianSheaf
  orderedCrossSpaceAbelianCechComplexIso abelianOpenSectionComparisonIso
  nativeIndependentSourceAmbientOrderedCechIso
/-- On original torsion-free coefficients,the section comparison is unchanged. -/
theorem nativeIndependentSourceAmbientCechSectionAddEquiv_general_eq_original
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (p : ℕ) (t : Fin (p+1) → ι) :
    nativeIndependentSourceAmbientCechSectionAddEquiv_general A B D hR hS a ha c hc hgenR hgenC p t =
      nativeIndependentSourceAmbientCechSectionAddEquiv A B D hR hS a ha c hc hgenR hgenC p t := by
  rfl
/-- Equality of the actual product-chart objects' specified isomorphisms. -/
theorem nativeIndependentSourceAmbientCechProductIso_general_eq_original
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (p : ℕ) (t : Fin (p+1) → ι) :
    nativeIndependentSourceAmbientCechProductIso_general A B D hR hS a ha c hc hgenR hgenC p t =
      nativeIndependentSourceAmbientCechProductIso A B D hR hS a ha c hc hgenR hgenC p t :=
  by
    simp only [nativeIndependentSourceAmbientCechProductIso_general,
      nativeIndependentSourceAmbientCechProductIso,
      nativeIndependentSourceAmbientCechSectionAddEquiv_general_eq_original]
/-- Equality on the SAME original intersection opens. -/
theorem nativeIndependentSourceAmbientCechIntersectionIso_general_eq_original
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (p : ℕ) (t : Fin (p+1) → ι) :
    nativeIndependentSourceAmbientCechIntersectionIso_general A B D hR hS a ha c hc hgenR hgenC p t =
      nativeIndependentSourceAmbientCechIntersectionIso A B D hR hS a ha c hc hgenR hgenC p t := by
  simp only [nativeIndependentSourceAmbientCechIntersectionIso_general,
    nativeIndependentSourceAmbientCechIntersectionIso,
    nativeIndependentSourceAmbientCechProductIso_general_eq_original]
/-- Equality of the complete original ordered Cech comparison,not a new choice. -/
theorem nativeIndependentSourceAmbientOrderedCechIso_general_eq_original
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) :
    nativeIndependentSourceAmbientOrderedCechIso_general A B D hR hS a ha c hc hgenR hgenC =
      nativeIndependentSourceAmbientOrderedCechIso A B D hR hS a ha c hc hgenR hgenC := by
  simp only [nativeIndependentSourceAmbientOrderedCechIso_general,
    nativeIndependentSourceAmbientOrderedCechBuilder_general,
    orderedCrossSpaceAbelianCechComplexIso_of_productCharts,
    nativeIndependentSourceAmbientOrderedCechIso,
    nativeIndependentSourceAmbientCechIntersectionIso,
    nativeIndependentSourceAmbientCechProductFamily_general,
    nativeCechProductOpen,nativeBaseSourceCechProductOpen,
    nativeIndependentSourceAmbientCechProductIso_general_eq_original]
/-- The SAME equality persists for every integer twist. -/
theorem nativeIndependentSourceAmbientOrderedTwistCechIso_general_eq_original
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (k : ℤ) :
    nativeIndependentSourceAmbientOrderedTwistCechIso_general A B D hR hS a ha c hc hgenR hgenC k =
      nativeIndependentSourceAmbientOrderedTwistCechIso A B D hR hS a ha c hc hgenR hgenC k := by
  simp only [nativeIndependentSourceAmbientOrderedTwistCechIso_general,
    nativeIndependentSourceAmbientOrderedTwistCechIso,
    nativeIndependentSourceAmbientOrderedCechIso_general_eq_original]
  rfl
end LinearStudy
