module
public import Linear.NativeIndependentSourceAmbientCechObjects
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
/-- Every ORIGINAL ordered coface commutes with the actual intersection
section isomorphisms.The change from product charts to limit intersections
is proved by equality transport,not assumed. -/
theorem nativeIndependentSourceAmbientCechIntersectionIso_face
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (p : ℕ) (k : Fin (p+2)) (t : OrderedCechIndex ι (p+1)) :
    let F := ((schemeModuleToActualAbelianSheaf (Proj A)).obj (nativeProjectiveModuleSheaf A D hR 0)).obj
    let G := ((schemeModuleToActualAbelianSheaf (Proj B)).obj (nativeProjectiveModuleSheaf B D hS 0)).obj
    let U := fun i => Proj.basicOpen A (a i)
    let V := fun i => Proj.basicOpen B (algebraMap R S (a i))
    (nativeIndependentSourceAmbientCechIntersectionIso A B D hR hS a ha c hc hgenR hgenC p (t.delete k).1).hom ≫
      G.map ((orderedCechFace V p k).φ t).op =
      F.map ((orderedCechFace U p k).φ t).op ≫
        (nativeIndependentSourceAmbientCechIntersectionIso A B D hR hS a ha c hc hgenR hgenC (p+1) t.1).hom := by
  let F := ((schemeModuleToActualAbelianSheaf (Proj A)).obj (nativeProjectiveModuleSheaf A D hR 0)).obj
  let G := ((schemeModuleToActualAbelianSheaf (Proj B)).obj (nativeProjectiveModuleSheaf B D hS 0)).obj
  let U := fun i => Proj.basicOpen A (a i)
  let V := fun i => Proj.basicOpen B (algebraMap R S (a i))
  let z0 := ∏ j : Fin (p+1),a ((t.delete k).1 j)
  let z1 := ∏ j : Fin (p+2),a (t.1 j)
  let fp : Proj.basicOpen A z1 ⟶ Proj.basicOpen A z0 := homOfLE (by
    dsimp only [z1,z0]
    rw [nativeCechCoordinateProduct_delete_mul a p t.1 k]
    exact ProjectiveSpectrum.basicOpen_mul_le_left A _ _)
  let gp : Proj.basicOpen B (algebraMap R S z1) ⟶ Proj.basicOpen B (algebraMap R S z0) := homOfLE (by
    dsimp only [z1,z0]
    rw [nativeCechCoordinateProduct_delete_mul a p t.1 k,map_mul]
    exact ProjectiveSpectrum.basicOpen_mul_le_left B _ _)
  let e0 := nativeIndependentSourceAmbientCechProductIso A B D hR hS a ha c hc hgenR hgenC p (t.delete k).1
  let e1 := nativeIndependentSourceAmbientCechProductIso A B D hR hS a ha c hc hgenR hgenC (p+1) t.1
  have he : e0.hom ≫ G.map gp.op = F.map fp.op ≫ e1.hom :=
    nativeIndependentSourceAmbientCechProductIso_delete A B D hR hS a ha c hc hgenR hgenC p t.1 k
  exact abelianOpenSectionComparisonIso_restrict F G _ _ _ _ _ _ _ _
    (nativeProjective_cechIntersection_eq_basicOpen A a p (t.delete k).1)
    (nativeProjective_cechIntersection_eq_basicOpen A a (p+1) t.1)
    (nativeSourceCoordinateCechIntersection_eq_basicOpen B a p (t.delete k).1)
    (nativeSourceCoordinateCechIntersection_eq_basicOpen B a (p+1) t.1)
    ((orderedCechFace U p k).φ t) fp ((orderedCechFace V p k).φ t) gp e0 e1 he
/-- The SAME original ordered Cech complexes of actual source/ambient native
sheaves are isomorphic in EVERY degree,including EVERY original restriction
and EVERY integer sign.No Cech/H or desired source-vanishing input. -/
def nativeIndependentSourceAmbientOrderedCechIso
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) :
    orderedTopAbelianCechComplex (Proj A) (fun i => Proj.basicOpen A (a i))
      ((schemeModuleToActualAbelianSheaf (Proj A)).obj (nativeProjectiveModuleSheaf A D hR 0)) ≅
      orderedTopAbelianCechComplex (Proj B) (fun i => Proj.basicOpen B (algebraMap R S (a i)))
        ((schemeModuleToActualAbelianSheaf (Proj B)).obj (nativeProjectiveModuleSheaf B D hS 0)) :=
  orderedCrossSpaceAbelianCechComplexIso _ _ _ _
    (fun p t => nativeIndependentSourceAmbientCechIntersectionIso A B D hR hS a ha c hc hgenR hgenC p t.1)
    (fun p k t => nativeIndependentSourceAmbientCechIntersectionIso_face A B D hR hS a ha c hc hgenR hgenC p k t)
end LinearStudy
