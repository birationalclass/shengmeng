module
public import Linear.OrderedCechDeleteValue
public import Linear.OrderedFreeSheafHomComplex
public import Linear.NativeGeneralSourceAmbientCechFaces
public import Linear.NativeFiniteGradedSourceAmbientCechObjects
public import Linear.SchemeModuleFiniteSupportCohomology
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
attribute [local irreducible] nativeWeightedSourceAmbientSectionAddEquiv
open CategoryTheory.Limits AlgebraicGeometry.Scheme.Modules
/-- The derived comparison is an isomorphism of the ACTUAL abelian-sheaf
section objects on the SAME original product charts. -/
def nativeIndependentSourceAmbientCechProductIso_general
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (p : ℕ) (t : Fin (p+1) → ι) :
    let F := ((schemeModuleToActualAbelianSheaf (Proj A)).obj (nativeProjectiveModuleSheaf A D hR 0)).obj
    let G := ((schemeModuleToActualAbelianSheaf (Proj B)).obj (nativeProjectiveModuleSheaf B D hS 0)).obj
    F.obj (op (Proj.basicOpen A (∏ j : Fin (p+1),a (t j)))) ≅
      G.obj (op (Proj.basicOpen B (algebraMap R S (∏ j : Fin (p+1),a (t j))))) :=
  (nativeIndependentSourceAmbientCechSectionAddEquiv_general A B D hR hS a ha c hc hgenR hgenC p t).toAddCommGrpIso
/-- The SAME comparison on actual intersection opens,via the proved product
identities.No replacement section objects or unspecified equivalences. -/
def nativeIndependentSourceAmbientCechIntersectionIso_general
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (p : ℕ) (t : Fin (p+1) → ι) :
    let F := ((schemeModuleToActualAbelianSheaf (Proj A)).obj (nativeProjectiveModuleSheaf A D hR 0)).obj
    let G := ((schemeModuleToActualAbelianSheaf (Proj B)).obj (nativeProjectiveModuleSheaf B D hS 0)).obj
    F.obj (op (∏ᶜ fun j : Fin (p+1) => Proj.basicOpen A (a (t j)))) ≅
      G.obj (op (∏ᶜ fun j : Fin (p+1) => Proj.basicOpen B (algebraMap R S (a (t j))))) := by
  let F := ((schemeModuleToActualAbelianSheaf (Proj A)).obj (nativeProjectiveModuleSheaf A D hR 0)).obj
  let G := ((schemeModuleToActualAbelianSheaf (Proj B)).obj (nativeProjectiveModuleSheaf B D hS 0)).obj
  exact abelianOpenSectionComparisonIso F G _ _ _ _
    (nativeProjective_cechIntersection_eq_basicOpen A a p t)
    (nativeSourceCoordinateCechIntersection_eq_basicOpen B a p t)
    (nativeIndependentSourceAmbientCechProductIso_general A B D hR hS a ha c hc hgenR hgenC p t)
/-- The previously proved ALL-deletion square is the square of the actual
abelian section morphisms,with its actual original open inclusions. -/
/- Actual proof term for the original abelian section-morphism square. -/
def nativeIndependentSourceAmbientCechProductIso_delete_general
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (p : ℕ) (t : Fin (p+2) → ι) (k : Fin (p+2)) :=
  let F := ((schemeModuleToActualAbelianSheaf (Proj A)).obj (nativeProjectiveModuleSheaf A D hR 0)).obj
  let G := ((schemeModuleToActualAbelianSheaf (Proj B)).obj (nativeProjectiveModuleSheaf B D hS 0)).obj
  let small := ∏ j : Fin (p+1),a (t (k.succAbove j))
  let big := ∏ j : Fin (p+2),a (t j)
  let g : Proj.basicOpen B (algebraMap R S big) ⟶ Proj.basicOpen B (algebraMap R S small) := homOfLE (by
    dsimp only [big,small]
    rw [nativeCechCoordinateProduct_delete_mul a p t k,map_mul]
    exact ProjectiveSpectrum.basicOpen_mul_le_left B _ _)
  let f : Proj.basicOpen A big ⟶ Proj.basicOpen A small := homOfLE (by
    dsimp only [big,small]
    rw [nativeCechCoordinateProduct_delete_mul a p t k]
    exact ProjectiveSpectrum.basicOpen_mul_le_left A _ _)
  ConcreteCategory.hom_ext
    ((nativeIndependentSourceAmbientCechProductIso_general A B D hR hS a ha c hc hgenR hgenC p
      (fun j => t (k.succAbove j))).hom ≫ G.map g.op)
    (F.map f.op ≫ (nativeIndependentSourceAmbientCechProductIso_general A B D hR hS a ha c hc hgenR hgenC (p+1) t).hom)
    (fun s => (nativeIndependentSourceAmbientCechSectionAddEquiv_delete_general A B D hR hS a ha c hc hgenR hgenC p t k s).symm)
/-- The same proved face square with its exact categorical type cached. -/
theorem nativeIndependentSourceAmbientCechProductIso_delete_general_typed
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (p : ℕ) (t : Fin (p+2) → ι) (k : Fin (p+2)) :
    let F := ((schemeModuleToActualAbelianSheaf (Proj A)).obj (nativeProjectiveModuleSheaf A D hR 0)).obj
    let G := ((schemeModuleToActualAbelianSheaf (Proj B)).obj (nativeProjectiveModuleSheaf B D hS 0)).obj
    let small := ∏ j : Fin (p+1),a (t (k.succAbove j))
    let big := ∏ j : Fin (p+2),a (t j)
    (nativeIndependentSourceAmbientCechProductIso_general A B D hR hS a ha c hc hgenR hgenC p (fun j => t (k.succAbove j))).hom ≫
      G.map (homOfLE (show Proj.basicOpen B (algebraMap R S big) ≤ Proj.basicOpen B (algebraMap R S small) from by
        dsimp only [big,small]
        rw [nativeCechCoordinateProduct_delete_mul a p t k,map_mul]
        exact ProjectiveSpectrum.basicOpen_mul_le_left B _ _)).op =
      F.map (homOfLE (show Proj.basicOpen A big ≤ Proj.basicOpen A small from by
        dsimp only [big,small]
        rw [nativeCechCoordinateProduct_delete_mul a p t k]
        exact ProjectiveSpectrum.basicOpen_mul_le_left A _ _)).op ≫
        (nativeIndependentSourceAmbientCechProductIso_general A B D hR hS a ha c hc hgenR hgenC (p+1) t).hom :=
  nativeIndependentSourceAmbientCechProductIso_delete_general A B D hR hS a ha c hc hgenR hgenC p t k
/-- The same product-chart square with the original ordered delete index cached. -/
theorem nativeIndependentSourceAmbientCechProductIso_orderedFace_general
    [LinearOrder ι] (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (p : ℕ) (k : Fin (p+2)) (t : OrderedCechIndex ι (p+1)) :
    let F := ((schemeModuleToActualAbelianSheaf (Proj A)).obj (nativeProjectiveModuleSheaf A D hR 0)).obj
    let G := ((schemeModuleToActualAbelianSheaf (Proj B)).obj (nativeProjectiveModuleSheaf B D hS 0)).obj
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
    (nativeIndependentSourceAmbientCechProductIso_general A B D hR hS a ha c hc hgenR hgenC p (t.delete k).1).hom ≫ G.map gp.op =
      F.map fp.op ≫ (nativeIndependentSourceAmbientCechProductIso_general A B D hR hS a ha c hc hgenR hgenC (p+1) t.1).hom :=
  by
    simpa only [orderedCechIndex_delete_values] using
      (nativeIndependentSourceAmbientCechProductIso_delete_general_typed A B D hR hS a ha c hc hgenR hgenC p t.1 k)
end LinearStudy
