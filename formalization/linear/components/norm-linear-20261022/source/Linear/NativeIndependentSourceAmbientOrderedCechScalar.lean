module
public import Linear.NativeIndependentSourceAmbientOrderedCech
public import Linear.NativeIndependentSourceAmbientCechIntersectionScalar
public import Linear.OrderedCrossSpaceCechEndomorphism
public import Linear.OrderedFreeSheafHomCoefficientNaturality
public import Linear.OrderedCrossSpaceAbelianCechIso
public import Linear.OrderedFreeSheafHomComplex
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
open AlgebraicGeometry.Scheme.Modules
variable [LinearOrder ι]
/-- The SAME existing cross-space ordered Cech comparison intertwines
ORIGINAL base-scalar coefficient maps. EVERY intersection square is derived
from actual product-chart scalars; original faces and signs are retained. -/
theorem nativeIndependentSourceAmbientOrderedCechIso_baseScalar
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (r : Γ(Spec (CommRingCat.of K),⊤)) :
    let MA := nativeProjectiveModuleSheaf A D hR 0
    let MB := nativeProjectiveModuleSheaf B D hS 0
    let piA := Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom (algebraMap K (A 0)))
    let piB := Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))
    let fA := (schemeModuleToActualAbelianSheaf (Proj A)).map
      (originalGlobalModuleScalar (piA.appTop r) MA)
    let fB := (schemeModuleToActualAbelianSheaf (Proj B)).map
      (originalGlobalModuleScalar (piB.appTop r) MB)
    (nativeIndependentSourceAmbientOrderedCechIso A B D hR hS a ha c hc hgenR hgenC).hom ≫
      orderedTopAbelianCechCoefficientMap (Proj B) (fun i => Proj.basicOpen B (algebraMap R S (a i))) fB =
    orderedTopAbelianCechCoefficientMap (Proj A) (fun i => Proj.basicOpen A (a i)) fA ≫
      (nativeIndependentSourceAmbientOrderedCechIso A B D hR hS a ha c hc hgenR hgenC).hom := by
  let MA := nativeProjectiveModuleSheaf A D hR 0
  let MB := nativeProjectiveModuleSheaf B D hS 0
  let F := ((schemeModuleToActualAbelianSheaf (Proj A)).obj MA).obj
  let G := ((schemeModuleToActualAbelianSheaf (Proj B)).obj MB).obj
  let piA := Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom (algebraMap K (A 0)))
  let piB := Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))
  let fA := (schemeModuleToActualAbelianSheaf (Proj A)).map
    (originalGlobalModuleScalar (piA.appTop r) MA)
  let fB := (schemeModuleToActualAbelianSheaf (Proj B)).map
    (originalGlobalModuleScalar (piB.appTop r) MB)
  exact orderedCrossSpaceAbelianCechComplexIso_endomorphism F G
    (fun i => Proj.basicOpen A (a i)) (fun i => Proj.basicOpen B (algebraMap R S (a i)))
    (fun p t => nativeIndependentSourceAmbientCechIntersectionIso A B D hR hS a ha c hc hgenR hgenC p t.1)
    (fun p k t => nativeIndependentSourceAmbientCechIntersectionIso_face A B D hR hS a ha c hc hgenR hgenC p k t)
    fA.hom fB.hom
    (fun p t => nativeIndependentSourceAmbientCechIntersectionIso_baseScalar A B D hR hS a ha c hc
      hgenR hgenC p t.1 r)
end LinearStudy
