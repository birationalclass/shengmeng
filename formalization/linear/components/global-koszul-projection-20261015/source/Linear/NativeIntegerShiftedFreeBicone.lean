module
public import Linear.NativeIntegerShiftedFreeCoordinateMaps
public import Linear.NativeProjectiveShiftedFreeSheafIdentities
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite Limits
variable {K S I : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [DecidableEq I] (w : I → ℤ) (k : ℤ)

/-- Every original coordinate summand is recovered at EVERY integer twist. -/
theorem nativeIntegerShiftedFree_inclusion_projection_self (i : I) :
    nativeIntegerShiftedFreeCoordinateInclusion 𝓑 w k i ≫
      nativeIntegerShiftedFreeCoordinateProjection 𝓑 w k i = 𝟙 _ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext p
  change (((nativeIntegerShiftedFreeCoordinateProjection 𝓑 w k i).val.app U)
    (((nativeIntegerShiftedFreeCoordinateInclusion 𝓑 w k i).val.app U) x)).1 p = x.1 p
  rw [nativeIntegerShiftedFreeCoordinateProjection_value,
    nativeIntegerShiftedFreeCoordinateInclusion_value]
  simpa using nativeShiftedFreePrime_projection_inclusion 𝓑 i i p.1 (x.1 p)

/-- Distinct original coordinate summands are orthogonal at EVERY integer twist. -/
theorem nativeIntegerShiftedFree_inclusion_projection_ne (i j : I) (hij : i ≠ j) :
    nativeIntegerShiftedFreeCoordinateInclusion 𝓑 w k i ≫
      nativeIntegerShiftedFreeCoordinateProjection 𝓑 w k j = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext p
  change (((nativeIntegerShiftedFreeCoordinateProjection 𝓑 w k j).val.app U)
    (((nativeIntegerShiftedFreeCoordinateInclusion 𝓑 w k i).val.app U) x)).1 p = 0
  rw [nativeIntegerShiftedFreeCoordinateProjection_value,
    nativeIntegerShiftedFreeCoordinateInclusion_value]
  simpa only [ite_eq_right hij] using
    nativeShiftedFreePrime_projection_inclusion 𝓑 i j p.1 (x.1 p)

/-- The actual coordinate maps exhaust the SAME associated sheaf at ANY integer twist. -/
theorem nativeIntegerShiftedFree_coordinate_total [Fintype I] :
    (∑ i : I, nativeIntegerShiftedFreeCoordinateProjection 𝓑 w k i ≫
      nativeIntegerShiftedFreeCoordinateInclusion 𝓑 w k i) = 𝟙 _ := by
  apply SheafOfModules.hom_ext
  change (SheafOfModules.forget _).map
    (∑ i : I, nativeIntegerShiftedFreeCoordinateProjection 𝓑 w k i ≫
      nativeIntegerShiftedFreeCoordinateInclusion 𝓑 w k i) =
    (SheafOfModules.forget _).map (𝟙 _)
  rw [Functor.map_sum, CategoryTheory.Functor.map_id]
  apply PresheafOfModules.hom_ext
  intro U
  change (PresheafOfModules.evaluation _ U).map
    (∑ i : I, (nativeIntegerShiftedFreeCoordinateProjection 𝓑 w k i ≫
      nativeIntegerShiftedFreeCoordinateInclusion 𝓑 w k i).val) =
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
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w) k).val.obj U →+
      nativeProjectiveModuleAtPrime (D := I → S) 𝓑 p.1 :=
    { toFun := fun y => y.1 p, map_zero' := rfl, map_add' := fun _ _ => rfl }
  change ev (∑ i : I, ((nativeIntegerShiftedFreeCoordinateProjection 𝓑 w k i ≫
    nativeIntegerShiftedFreeCoordinateInclusion 𝓑 w k i).val.app U).hom x) = x.1 p
  rw [map_sum]
  have hterm (i : I) :
      ev (((nativeIntegerShiftedFreeCoordinateProjection 𝓑 w k i ≫
        nativeIntegerShiftedFreeCoordinateInclusion 𝓑 w k i).val.app U).hom x) =
      nativeProjectiveModuleAtPrimeMap 𝓑
        (LinearMap.single (R := S) (φ := fun _ : I => S) i) p.1
          (nativeProjectiveModuleAtPrimeMap 𝓑
            (LinearMap.proj (R := S) (φ := fun _ : I => S) i) p.1 (x.1 p)) := by
    change (((nativeIntegerShiftedFreeCoordinateInclusion 𝓑 w k i).val.app U)
      (((nativeIntegerShiftedFreeCoordinateProjection 𝓑 w k i).val.app U) x)).1 p = _
    rw [nativeIntegerShiftedFreeCoordinateInclusion_value,
      nativeIntegerShiftedFreeCoordinateProjection_value]
  simp_rw [hterm]
  exact nativeShiftedFreePrime_coordinate_total 𝓑 p.1 (x.1 p)

/-- Bicone built from the SAME original integer-twist coordinate maps. -/
def nativeIntegerShiftedFreeBicone : Bicone (fun i : I =>
    nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (k-w i)) where
  pt := nativeProjectiveModuleSheaf 𝓑 (integerShiftedFreePiece 𝓑 w)
    (integerShiftedFreePiece_smul_homogeneous 𝓑 w) k
  π := nativeIntegerShiftedFreeCoordinateProjection 𝓑 w k
  ι := nativeIntegerShiftedFreeCoordinateInclusion 𝓑 w k
  ι_π i j := by
    by_cases hij : i = j
    · subst j
      simpa using nativeIntegerShiftedFree_inclusion_projection_self 𝓑 w k i
    · simpa only [dite_eq_right hij] using
        nativeIntegerShiftedFree_inclusion_projection_ne 𝓑 w k i j hij

/-- Both universal properties are derived from the actual finite coordinate identity. -/
def nativeIntegerShiftedFreeBiconeIsBilimit [Fintype I] :
    (nativeIntegerShiftedFreeBicone 𝓑 w k).IsBilimit :=
  isBilimitOfTotal (nativeIntegerShiftedFreeBicone 𝓑 w k)
    (nativeIntegerShiftedFree_coordinate_total 𝓑 w k)

/-- The constructed original bicone supplies the actual finite biproduct. -/
@[instance] def nativeIntegerShiftedFreeHasBiproduct [Fintype I] :
    HasBiproduct (fun i : I =>
      nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) (k-w i)) :=
  ⟨⟨nativeIntegerShiftedFreeBicone 𝓑 w k,
    nativeIntegerShiftedFreeBiconeIsBilimit 𝓑 w k⟩⟩

/-- Actual finite biproduct presentation with the original coordinates at EVERY integer k. -/
def nativeIntegerShiftedFreeBiproductIso [Fintype I] :
    nativeProjectiveModuleSheaf 𝓑 (integerShiftedFreePiece 𝓑 w)
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w) k ≅
    biproduct (fun i : I =>
      nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) (k-w i)) :=
  biproduct.uniqueUpToIso _ (nativeIntegerShiftedFreeBiconeIsBilimit 𝓑 w k)

end LinearStudy
