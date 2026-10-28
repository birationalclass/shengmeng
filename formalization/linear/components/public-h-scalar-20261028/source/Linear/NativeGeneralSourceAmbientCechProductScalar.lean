module
public import Linear.NativeGeneralSourceAmbientCechProductScalarProof
public import Linear.NativeGeneralSourceAmbientCechObjects
public import Linear.NativeGeneralSourceAmbientOriginalBaseScalarTyped
public import Linear.SchemeModuleActualAbelianScalarValue
public import Linear.NativeProjectiveModuleBaseScalarValue
public import Linear.ConcreteAdditiveEquivSquare
public import Linear.NativeFiniteGradedSourceAmbientCechObjects
public import Linear.SchemeModuleFiniteSupportCohomology
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
attribute [local irreducible] originalGlobalModuleScalar
  nativeIndependentSourceAmbientCechSectionAddEquiv_general
set_option diagnostics true
set_option diagnostics.threshold 500
attribute [local irreducible] nativeWeightedSourceAmbientSectionAddEquiv nativeProjectiveModuleSheaf nativeProjectiveModulePresheaf schemeModuleToActualAbelianSheaf
  nativeProjectiveModuleSections nativeProjectiveChartDegreeZeroSectionMap
/-- The SAME actual product-chart isomorphism intertwines the two
ORIGINAL sheaf coefficient scalar maps, with the actual Proj-to-Spec K
structure maps. No coefficient or global-H square is assumed. -/
theorem nativeIndependentSourceAmbientCechProductIso_baseScalar_general
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (p : ℕ) (t : Fin (p+1) → ι) (r : Γ(Spec (CommRingCat.of K),⊤)) :
    let MA := nativeProjectiveModuleSheaf A D hR 0
    let MB := nativeProjectiveModuleSheaf B D hS 0
    let piA := Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom (algebraMap K (A 0)))
    let piB := Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))
    let fA := ((schemeModuleToActualAbelianSheaf (Proj A)).map
      (originalGlobalModuleScalar (piA.appTop r) MA)).hom
    let fB := ((schemeModuleToActualAbelianSheaf (Proj B)).map
      (originalGlobalModuleScalar (piB.appTop r) MB)).hom
    (nativeIndependentSourceAmbientCechProductIso_general A B D hR hS a ha c hc hgenR hgenC p t).hom ≫
      fB.app (op (Proj.basicOpen B (algebraMap R S (∏ j : Fin (p+1),a (t j))))) =
    fA.app (op (Proj.basicOpen A (∏ j : Fin (p+1),a (t j)))) ≫
      (nativeIndependentSourceAmbientCechProductIso_general A B D hR hS a ha c hc hgenR hgenC p t).hom :=
  nativeIndependentSourceAmbientCechProductIso_baseScalar_general_proof A B D hR hS a ha c hc
    hgenR hgenC p t r
end LinearStudy
