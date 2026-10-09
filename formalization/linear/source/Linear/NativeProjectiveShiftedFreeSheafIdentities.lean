module
public import Linear.NativeProjectiveShiftedFreeSheafMaps
public import Linear.NativeProjectiveShiftedFreePrimeIdentities
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Preadditive.Biproducts
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite Limits
universe u
variable {K S ι : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [DecidableEq ι] (w : ι → ℤ)

/-- The actual native twist summand is recovered by its own original
coordinate inclusion and projection. -/
theorem nativeShiftedFreeSheaf_inclusion_projection_self (i : ι) :
    nativeShiftedFreeCoordinateSheafInclusion 𝓑 w i ≫
      nativeShiftedFreeCoordinateSheafProjection 𝓑 w i = 𝟙 _ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext p
  change nativeProjectiveModuleAtPrimeMap 𝓑
    (LinearMap.proj (R := S) (φ := fun _ : ι => S) i) p.1
      (nativeProjectiveModuleAtPrimeMap 𝓑
        (LinearMap.single (R := S) (φ := fun _ : ι => S) i) p.1 (x.1 p)) = x.1 p
  simpa using
    nativeShiftedFreePrime_projection_inclusion 𝓑 i i p.1 (x.1 p)

/-- Different actual native coordinate summands are orthogonal. -/
theorem nativeShiftedFreeSheaf_inclusion_projection_ne (i j : ι) (hij : i ≠ j) :
    nativeShiftedFreeCoordinateSheafInclusion 𝓑 w i ≫
      nativeShiftedFreeCoordinateSheafProjection 𝓑 w j = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext p
  change nativeProjectiveModuleAtPrimeMap 𝓑
    (LinearMap.proj (R := S) (φ := fun _ : ι => S) j) p.1
      (nativeProjectiveModuleAtPrimeMap 𝓑
        (LinearMap.single (R := S) (φ := fun _ : ι => S) i) p.1 (x.1 p)) = 0
  simpa only [ite_eq_right hij] using
    nativeShiftedFreePrime_projection_inclusion 𝓑 i j p.1 (x.1 p)

/-- The actual native coordinate summands exhaust the associated sheaf
of the actual finite shifted free module. -/
theorem nativeShiftedFreeSheaf_coordinate_total [Fintype ι] :
    (∑ i : ι, nativeShiftedFreeCoordinateSheafProjection 𝓑 w i ≫
      nativeShiftedFreeCoordinateSheafInclusion 𝓑 w i) = 𝟙 _ := by
  apply SheafOfModules.hom_ext
  change (SheafOfModules.forget _).map
    (∑ i : ι, nativeShiftedFreeCoordinateSheafProjection 𝓑 w i ≫
      nativeShiftedFreeCoordinateSheafInclusion 𝓑 w i) =
    (SheafOfModules.forget _).map (𝟙 _)
  rw [Functor.map_sum, CategoryTheory.Functor.map_id]
  apply PresheafOfModules.hom_ext
  intro U
  change (PresheafOfModules.evaluation _ U).map
    (∑ i : ι, (nativeShiftedFreeCoordinateSheafProjection 𝓑 w i ≫
      nativeShiftedFreeCoordinateSheafInclusion 𝓑 w i).val) =
    (PresheafOfModules.evaluation _ U).map (𝟙 _)
  rw [Functor.map_sum, CategoryTheory.Functor.map_id]
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_sum]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.sum_apply]
  apply Subtype.ext
  funext p
  let ev : (nativeProjectiveModuleSheaf 𝓑 (integerShiftedFreePiece 𝓑 w)
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w) 0).val.obj U →+
      nativeProjectiveModuleAtPrime (D := ι → S) 𝓑 p.1 :=
    { toFun := fun y => y.1 p, map_zero' := rfl, map_add' := fun _ _ => rfl }
  change ev (∑ i : ι, ((nativeShiftedFreeCoordinateSheafProjection 𝓑 w i ≫
    nativeShiftedFreeCoordinateSheafInclusion 𝓑 w i).val.app U).hom x) = x.1 p
  rw [map_sum]
  change (∑ i : ι, nativeProjectiveModuleAtPrimeMap 𝓑
    (LinearMap.single (R := S) (φ := fun _ : ι => S) i) p.1
    (nativeProjectiveModuleAtPrimeMap 𝓑
      (LinearMap.proj (R := S) (φ := fun _ : ι => S) i) p.1 (x.1 p))) = x.1 p
  exact nativeShiftedFreePrime_coordinate_total 𝓑 p.1 (x.1 p)

end LinearStudy
