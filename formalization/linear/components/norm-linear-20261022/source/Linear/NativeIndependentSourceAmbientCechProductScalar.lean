module
public import Linear.NativeIndependentSourceAmbientCechObjects
public import Linear.NativeIndependentSourceAmbientCechBaseScalar
public import Linear.SchemeModuleActualAbelianScalarValue
public import Linear.NativeProjectiveModuleBaseScalarValue
public import Linear.ConcreteAdditiveEquivSquare
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
attribute [local irreducible] originalGlobalModuleScalar
  nativeIndependentSourceAmbientCechSectionAddEquiv
set_option diagnostics true
set_option diagnostics.threshold 500
/-- The SAME actual product-chart isomorphism intertwines the two
ORIGINAL sheaf coefficient scalar maps, with the actual Proj-to-Spec K
structure maps. No coefficient or global-H square is assumed. -/
theorem nativeIndependentSourceAmbientCechProductIso_baseScalar
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
    (nativeIndependentSourceAmbientCechProductIso A B D hR hS a ha c hc hgenR hgenC p t).hom ≫
      fB.app (op (Proj.basicOpen B (algebraMap R S (∏ j : Fin (p+1),a (t j))))) =
    fA.app (op (Proj.basicOpen A (∏ j : Fin (p+1),a (t j)))) ≫
      (nativeIndependentSourceAmbientCechProductIso A B D hR hS a ha c hc hgenR hgenC p t).hom := by
  let MA := nativeProjectiveModuleSheaf A D hR 0
  let MB := nativeProjectiveModuleSheaf B D hS 0
  let piA := Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom (algebraMap K (A 0)))
  let piB := Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))
  let UA := Proj.basicOpen A (∏ j : Fin (p+1),a (t j))
  let UB := Proj.basicOpen B (algebraMap R S (∏ j : Fin (p+1),a (t j)))
  let fA := ((schemeModuleToActualAbelianSheaf (Proj A)).map
    (originalGlobalModuleScalar (piA.appTop r) MA)).hom
  let fB := ((schemeModuleToActualAbelianSheaf (Proj B)).map
    (originalGlobalModuleScalar (piB.appTop r) MB)).hom
  let E := nativeIndependentSourceAmbientCechSectionAddEquiv A B D hR hS a ha c hc hgenR hgenC p t
  apply additiveEquivIso_endomorphism E (fA.app (op UA)) (fB.app (op UB))
  intro s
  calc
    E (fA.app (op UA) s) = E (nativeProjectiveModuleScalarApply A D hR 0 (op UA)
        (projBasicOpenBaseScalar A (algebraMap K (A 0)) (∏ j : Fin (p+1),a (t j)) r) s) :=
      congrArg E (nativeProjectiveModuleActualBaseScalar_app A D hR 0 (∏ j : Fin (p+1),a (t j)) r s)
    _ = nativeProjectiveModuleScalarApply B D hS 0 (op UB)
        (projBasicOpenBaseScalar B (algebraMap K (B 0)) (algebraMap R S (∏ j : Fin (p+1),a (t j))) r)
        (E s) := nativeIndependentSourceAmbientCechSectionAddEquiv_baseScalar A B D hR hS a ha c hc
          hgenR hgenC p t r s
    _ = fB.app (op UB) (E s) :=
      (nativeProjectiveModuleActualBaseScalar_app B D hS 0
        (algebraMap R S (∏ j : Fin (p+1),a (t j))) r (E s)).symm
end LinearStudy
