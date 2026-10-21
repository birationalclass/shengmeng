module
public import Linear.NativeIndependentSourceAmbientCechProductScalar
public import Linear.OrderedCrossSpaceCechEndomorphism
public import Linear.NativeIndependentSourceAmbientCechBaseScalar
public import Linear.SchemeModuleActualAbelianScalarValue
public import Linear.NativeFiniteGradedSourceAmbientCechObjects
public import Linear.SchemeModuleFiniteSupportCohomology
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
variable [AddCommGroup M] [Module K M] [Module R M] [Module S M]
variable [IsScalarTower R S M] [IsScalarTower K R M] [IsScalarTower K S M]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (B : ℕ → Submodule K S) [GradedAlgebra B] [SetLike.GradedSMul A B]
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hR : ∀ n : ℕ,∀ j : ℤ,∀ c : R,c ∈ A n → ∀ x : M,x ∈ D j → c • x ∈ D ((n : ℤ)+j))
variable (hS : ∀ n : ℕ,∀ j : ℤ,∀ c : S,c ∈ B n → ∀ x : M,x ∈ D j → c • x ∈ D ((n : ℤ)+j))
variable [IsDomain S] [Module.IsTorsionFree S M]
variable [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite R M] [Module.Finite S M]
variable {ι : Type u} (a : ι → R) (ha : ∀ i,a i ∈ A 1)
variable {κ : Type u} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
include c hc
attribute [local instance] nativeHomogeneousAwayModuleScalar LocalizedModule.moduleOfIsLocalization
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
open CategoryTheory.Limits
/-- Original intersection opens retain the derived actual base-scalar
coefficient square by equality transport from original product charts. -/
theorem nativeIndependentSourceAmbientCechIntersectionIso_baseScalar
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
    (nativeIndependentSourceAmbientCechIntersectionIso A B D hR hS a ha c hc hgenR hgenC p t).hom ≫
      fB.app (op (∏ᶜ fun j : Fin (p+1) => Proj.basicOpen B (algebraMap R S (a (t j))))) =
    fA.app (op (∏ᶜ fun j : Fin (p+1) => Proj.basicOpen A (a (t j)))) ≫
      (nativeIndependentSourceAmbientCechIntersectionIso A B D hR hS a ha c hc hgenR hgenC p t).hom := by
  let MA := nativeProjectiveModuleSheaf A D hR 0
  let MB := nativeProjectiveModuleSheaf B D hS 0
  let F := ((schemeModuleToActualAbelianSheaf (Proj A)).obj MA).obj
  let G := ((schemeModuleToActualAbelianSheaf (Proj B)).obj MB).obj
  let piA := Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom (algebraMap K (A 0)))
  let piB := Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))
  let fA := ((schemeModuleToActualAbelianSheaf (Proj A)).map
    (originalGlobalModuleScalar (piA.appTop r) MA)).hom
  let fB := ((schemeModuleToActualAbelianSheaf (Proj B)).map
    (originalGlobalModuleScalar (piB.appTop r) MB)).hom
  exact abelianOpenSectionComparisonIso_endomorphism F G
    _ _ _ _ (nativeProjective_cechIntersection_eq_basicOpen A a p t)
    (nativeSourceCoordinateCechIntersection_eq_basicOpen B a p t)
    (nativeIndependentSourceAmbientCechProductIso A B D hR hS a ha c hc hgenR hgenC p t)
    fA fB (nativeIndependentSourceAmbientCechProductIso_baseScalar A B D hR hS a ha c hc
      hgenR hgenC p t r)
end LinearStudy
