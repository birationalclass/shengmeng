module
public import Linear.NativeWeightedSourceAmbientSectionNamedOverlap
public import Linear.NativeFiniteGradedSourceAmbientCechSections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
/-- Finite coordinate products split at ANY deleted coordinate,with the
remaining product retaining its actual degree. -/
theorem nativeCechCoordinateProduct_delete_mul {R ι : Type u} [CommMonoid R]
    (a : ι → R) (p : ℕ) (t : Fin (p+2) → ι) (k : Fin (p+2)) :
    (∏ j : Fin (p+2),a (t j)) =
      (∏ j : Fin (p+1),a (t (k.succAbove j))) * a (t k) := by
  rw [Fin.prod_univ_succAbove _ k,mul_comm]
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
attribute [local irreducible] nativeWeightedSourceAmbientSectionAddEquiv
/-- EVERY actual deletion-face restriction commutes with the derived
source/ambient section equivalences.Not merely first/pairwise overlaps:
this holds for every p,every original tuple and every deleted coordinate. -/
theorem nativeFiniteGradedSourceAmbientCechSectionAddEquiv_delete
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenS : Algebra.adjoin K (Set.range (fun i => algebraMap R S (a i))) = ⊤)
    (p : ℕ) (t : Fin (p+2) → ι) (k : Fin (p+2))
    (s : nativeProjectiveModuleSections A D hR 0
      (op (Proj.basicOpen A (∏ j : Fin (p+1),a (t (k.succAbove j)))))) :
    nativeFiniteGradedSourceAmbientCechSectionAddEquiv A B D hR hS a ha hgenR hgenS (p+1) t
      ((nativeProjectiveModulePresheaf A D hR 0).map
        (homOfLE (show Proj.basicOpen A (∏ j : Fin (p+2),a (t j)) ≤
          Proj.basicOpen A (∏ j : Fin (p+1),a (t (k.succAbove j))) from by
            rw [nativeCechCoordinateProduct_delete_mul a p t k]
            exact ProjectiveSpectrum.basicOpen_mul_le_left A _ _)).op s) =
      (nativeProjectiveModulePresheaf B D hS 0).map
        (homOfLE (show Proj.basicOpen B (algebraMap R S (∏ j : Fin (p+2),a (t j))) ≤
          Proj.basicOpen B (algebraMap R S (∏ j : Fin (p+1),a (t (k.succAbove j)))) from by
            rw [nativeCechCoordinateProduct_delete_mul a p t k,map_mul]
            exact ProjectiveSpectrum.basicOpen_mul_le_left B _ _)).op
        (nativeFiniteGradedSourceAmbientCechSectionAddEquiv A B D hR hS a ha hgenR hgenS p
          (fun j => t (k.succAbove j)) s) := by
  let c := ∏ j : Fin (p+1),a (t (k.succAbove j))
  let z := ∏ j : Fin (p+2),a (t j)
  have hc : c ∈ A (p+1) := nativeProjective_cechProduct_mem_degree A a ha p (fun j => t (k.succAbove j))
  have hz : z ∈ A (p+1+1) := nativeProjective_cechProduct_mem_degree A a ha (p+1) t
  have h0 := nativeFiniteGradedAmbientCechProductSectionMap_bijective A B D hR a ha hgenR p
    (fun j => t (k.succAbove j))
  have h1 := nativeFiniteGradedSourceCechProductSectionMap_bijective A B D hS a ha hgenS p
    (fun j => t (k.succAbove j))
  have h2 := nativeFiniteGradedAmbientCechProductSectionMap_bijective A B D hR a ha hgenR (p+1) t
  have h3 := nativeFiniteGradedSourceCechProductSectionMap_bijective A B D hS a ha hgenS (p+1) t
  exact nativeWeightedSourceAmbientSectionAddEquiv_overlap_named A B D hR hS (p+1) 1 c (a (t k)) z
    hc (ha (t k)) hz (nativeCechCoordinateProduct_delete_mul a p t k) h0 h1 h2 h3 s
end LinearStudy
