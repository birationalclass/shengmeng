module
public import Linear.NativeProjectiveShiftedFreeCoordinateMaps
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S ι : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [DecidableEq ι] (w : ι → ℤ)

/-- Actual natural projection from the native associated presheaf of
the shifted free module to its actual integer-twist summand. -/
def nativeShiftedFreeCoordinatePresheafProjection (i : ι) :
    nativeProjectiveModulePresheaf 𝓑 (integerShiftedFreePiece 𝓑 w)
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w) 0 ⟶
      nativeProjectiveModulePresheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) (-w i) where
  app U := by
    letI := nativeProjectiveModuleSectionGroup 𝓑 (integerShiftedFreePiece 𝓑 w)
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w) 0 U
    letI := nativeProjectiveModuleSectionModule 𝓑 (integerShiftedFreePiece 𝓑 w)
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w) 0 U
    letI := nativeProjectiveModuleSectionGroup 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (-w i) U
    letI := nativeProjectiveModuleSectionModule 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (-w i) U
    exact ModuleCat.ofHom (nativeShiftedFreeCoordinateSectionProjection 𝓑 w i U)
  naturality f := by
    apply ModuleCat.hom_ext
    rfl

/-- Actual natural inclusion of a native integer twist into the native
associated presheaf of the original shifted free module. -/
def nativeShiftedFreeCoordinatePresheafInclusion (i : ι) :
    nativeProjectiveModulePresheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (-w i) ⟶
      nativeProjectiveModulePresheaf 𝓑 (integerShiftedFreePiece 𝓑 w)
        (integerShiftedFreePiece_smul_homogeneous 𝓑 w) 0 where
  app U := by
    letI := nativeProjectiveModuleSectionGroup 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (-w i) U
    letI := nativeProjectiveModuleSectionModule 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (-w i) U
    letI := nativeProjectiveModuleSectionGroup 𝓑 (integerShiftedFreePiece 𝓑 w)
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w) 0 U
    letI := nativeProjectiveModuleSectionModule 𝓑 (integerShiftedFreePiece 𝓑 w)
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w) 0 U
    exact ModuleCat.ofHom (nativeShiftedFreeCoordinateSectionInclusion 𝓑 w i U)
  naturality f := by
    apply ModuleCat.hom_ext
    rfl

/-- The genuine projection on native sheaves on the original Proj. -/
def nativeShiftedFreeCoordinateSheafProjection (i : ι) :
    nativeProjectiveModuleSheaf 𝓑 (integerShiftedFreePiece 𝓑 w)
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w) 0 ⟶
      nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) (-w i) where
  val := nativeShiftedFreeCoordinatePresheafProjection 𝓑 w i

/-- The genuine inclusion on native sheaves on the original Proj. -/
def nativeShiftedFreeCoordinateSheafInclusion (i : ι) :
    nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (-w i) ⟶
      nativeProjectiveModuleSheaf 𝓑 (integerShiftedFreePiece 𝓑 w)
        (integerShiftedFreePiece_smul_homogeneous 𝓑 w) 0 where
  val := nativeShiftedFreeCoordinatePresheafInclusion 𝓑 w i

end LinearStudy
