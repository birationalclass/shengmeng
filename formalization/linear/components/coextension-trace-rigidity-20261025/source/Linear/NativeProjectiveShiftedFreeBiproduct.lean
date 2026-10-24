module
public import Linear.NativeProjectiveShiftedFreeSheafIdentities
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

/-- The actual associated sheaf of the shifted free module, with its
constructed original coordinate maps, is a bicone of native twists. -/
def nativeShiftedFreeBicone : Bicone (fun i : ι =>
    nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (-w i)) where
  pt := nativeProjectiveModuleSheaf 𝓑 (integerShiftedFreePiece 𝓑 w)
    (integerShiftedFreePiece_smul_homogeneous 𝓑 w) 0
  π := nativeShiftedFreeCoordinateSheafProjection 𝓑 w
  ι := nativeShiftedFreeCoordinateSheafInclusion 𝓑 w
  ι_π i j := by
    by_cases hij : i = j
    · subst j
      simpa using nativeShiftedFreeSheaf_inclusion_projection_self 𝓑 w i
    · simpa only [dite_eq_right hij] using
        nativeShiftedFreeSheaf_inclusion_projection_ne 𝓑 w i j hij

/-- Both universal properties follow from the proven actual finite
coordinate identity; no free-sheaf comparison is an input. -/
def nativeShiftedFreeBiconeIsBilimit [Fintype ι] :
    (nativeShiftedFreeBicone 𝓑 w).IsBilimit :=
  isBilimitOfTotal (nativeShiftedFreeBicone 𝓑 w)
    (nativeShiftedFreeSheaf_coordinate_total 𝓑 w)

/-- The constructed bicone supplies the actual finite biproduct. -/
@[instance] def nativeShiftedFreeHasBiproduct [Fintype ι] :
    HasBiproduct (fun i : ι =>
      nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) (-w i)) :=
  ⟨⟨nativeShiftedFreeBicone 𝓑 w, nativeShiftedFreeBiconeIsBilimit 𝓑 w⟩⟩

/-- Genuine native shifted-free associated sheaf comparison with the
finite biproduct of the actual native integer-twist sheaves. -/
def nativeShiftedFreeSheafBiproductIso [Fintype ι] :
    nativeProjectiveModuleSheaf 𝓑 (integerShiftedFreePiece 𝓑 w)
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w) 0 ≅
    biproduct (fun i : ι =>
      nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) (-w i)) :=
  biproduct.uniqueUpToIso _ (nativeShiftedFreeBiconeIsBilimit 𝓑 w)

end LinearStudy
