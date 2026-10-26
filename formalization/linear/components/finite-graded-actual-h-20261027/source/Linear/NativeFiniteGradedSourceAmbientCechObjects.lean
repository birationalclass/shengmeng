module
public import Linear.NativeFiniteGradedSourceAmbientCechFaces
public import Linear.AbelianOpenSectionIsoTransport
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
attribute [local instance] nativeHomogeneousAwayModuleScalar LocalizedModule.moduleOfIsLocalization
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
open CategoryTheory.Limits
/-- Source coordinate intersections equal the basic open of the image of
its ORIGINAL base-coordinate product,in every finite degree. -/
theorem nativeSourceCoordinateCechIntersection_eq_basicOpen
    (p : ℕ) (t : Fin (p+1) → ι) :
    (∏ᶜ fun j : Fin (p+1) => Proj.basicOpen B (algebraMap R S (a (t j)))) =
      Proj.basicOpen B (algebraMap R S (∏ j : Fin (p+1),a (t j))) :=
  (nativeProjective_cechIntersection_eq_basicOpen B (fun i => algebraMap R S (a i)) p t).trans
    (congrArg (Proj.basicOpen B) (map_prod (algebraMap R S) (fun j : Fin (p+1) => a (t j)) Finset.univ).symm)
/-- The derived comparison is an isomorphism of the ACTUAL abelian-sheaf
section objects on the SAME original product charts. -/
def nativeFiniteGradedSourceAmbientCechProductIso
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenS : Algebra.adjoin K (Set.range (fun i => algebraMap R S (a i))) = ⊤)
    (p : ℕ) (t : Fin (p+1) → ι) :
    let F := ((schemeModuleToActualAbelianSheaf (Proj A)).obj (nativeProjectiveModuleSheaf A D hR 0)).obj
    let G := ((schemeModuleToActualAbelianSheaf (Proj B)).obj (nativeProjectiveModuleSheaf B D hS 0)).obj
    F.obj (op (Proj.basicOpen A (∏ j : Fin (p+1),a (t j)))) ≅
      G.obj (op (Proj.basicOpen B (algebraMap R S (∏ j : Fin (p+1),a (t j))))) :=
  (nativeFiniteGradedSourceAmbientCechSectionAddEquiv A B D hR hS a ha hgenR hgenS p t).toAddCommGrpIso
/-- The SAME comparison on actual intersection opens,via the proved product
identities.No replacement section objects or unspecified equivalences. -/
def nativeFiniteGradedSourceAmbientCechIntersectionIso
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenS : Algebra.adjoin K (Set.range (fun i => algebraMap R S (a i))) = ⊤)
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
    (nativeFiniteGradedSourceAmbientCechProductIso A B D hR hS a ha hgenR hgenS p t)
/-- The previously proved ALL-deletion square is the square of the actual
abelian section morphisms,with its actual original open inclusions. -/
theorem nativeFiniteGradedSourceAmbientCechProductIso_delete
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenS : Algebra.adjoin K (Set.range (fun i => algebraMap R S (a i))) = ⊤)
    (p : ℕ) (t : Fin (p+2) → ι) (k : Fin (p+2)) :
    let F := ((schemeModuleToActualAbelianSheaf (Proj A)).obj (nativeProjectiveModuleSheaf A D hR 0)).obj
    let G := ((schemeModuleToActualAbelianSheaf (Proj B)).obj (nativeProjectiveModuleSheaf B D hS 0)).obj
    let small := ∏ j : Fin (p+1),a (t (k.succAbove j))
    let big := ∏ j : Fin (p+2),a (t j)
    (nativeFiniteGradedSourceAmbientCechProductIso A B D hR hS a ha hgenR hgenS p (fun j => t (k.succAbove j))).hom ≫
      G.map (homOfLE (show Proj.basicOpen B (algebraMap R S big) ≤ Proj.basicOpen B (algebraMap R S small) from by
        dsimp only [big,small]
        rw [nativeCechCoordinateProduct_delete_mul a p t k,map_mul]
        exact ProjectiveSpectrum.basicOpen_mul_le_left B _ _)).op =
      F.map (homOfLE (show Proj.basicOpen A big ≤ Proj.basicOpen A small from by
        dsimp only [big,small]
        rw [nativeCechCoordinateProduct_delete_mul a p t k]
        exact ProjectiveSpectrum.basicOpen_mul_le_left A _ _)).op ≫
        (nativeFiniteGradedSourceAmbientCechProductIso A B D hR hS a ha hgenR hgenS (p+1) t).hom := by
  ext s
  exact (nativeFiniteGradedSourceAmbientCechSectionAddEquiv_delete A B D hR hS a ha hgenR hgenS p t k s).symm
end LinearStudy
