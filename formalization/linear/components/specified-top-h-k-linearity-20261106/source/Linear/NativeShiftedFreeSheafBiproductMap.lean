module
public import Linear.NativeProjectiveShiftedFreeBiproduct
public import Linear.NativeProjectiveDegreeZeroMap
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
section Coordinates
variable {K S ι : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [Fintype ι] [DecidableEq ι] (w : ι → ℤ)

/-- The inverse of the ACTUAL shifted-free comparison respects the
original single-coordinate sheaf inclusion. -/
theorem nativeShiftedFreeSheafBiproductIso_inclusion (i : ι) :
    biproduct.ι (fun j : ι => nativeProjectiveModuleSheaf 𝓑
      (nativeProjectiveRingIntegerPiece 𝓑) (nativeProjectiveRingIntegerPiece_graded 𝓑) (-w j)) i ≫
      (nativeShiftedFreeSheafBiproductIso 𝓑 w).inv =
        nativeShiftedFreeCoordinateSheafInclusion 𝓑 w i := by
  simp [nativeShiftedFreeSheafBiproductIso,biproduct.uniqueUpToIso,nativeShiftedFreeBicone]

/-- The ACTUAL shifted-free comparison respects the original coordinate
sheaf projection. -/
theorem nativeShiftedFreeSheafBiproductIso_projection (i : ι) :
    (nativeShiftedFreeSheafBiproductIso 𝓑 w).hom ≫
      biproduct.π (fun j : ι => nativeProjectiveModuleSheaf 𝓑
        (nativeProjectiveRingIntegerPiece 𝓑) (nativeProjectiveRingIntegerPiece_graded 𝓑) (-w j)) i =
      nativeShiftedFreeCoordinateSheafProjection 𝓑 w i := by
  simp [nativeShiftedFreeSheafBiproductIso,biproduct.uniqueUpToIso,nativeShiftedFreeBicone]
end Coordinates

section Matrix
variable {K S I J : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (z : I → ℤ) (w : J → ℤ) (c : (I → S) →ₗ[S] (J → S))
variable (hh : ∀ d : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece 𝓑 z d →
  c x ∈ integerShiftedFreePiece 𝓑 w d)

/-- The ORIGINAL degree-zero sheaf map between shifted finite free
modules is its matrix of ORIGINAL coordinate components under the
constructed biproduct comparisons. It is not defined through this
identity or through duality. Polynomial multiplication comparison and
integer regrading remain separate obligations. -/
theorem nativeShiftedFreeSheafMap_biproductMatrix :
    (nativeShiftedFreeSheafBiproductIso 𝓑 z).inv ≫
      nativeProjectiveDegreeZeroSheafMap 𝓑 (integerShiftedFreePiece 𝓑 z)
        (integerShiftedFreePiece 𝓑 w) (integerShiftedFreePiece_smul_homogeneous 𝓑 z)
        (integerShiftedFreePiece_smul_homogeneous 𝓑 w) c hh 0 ≫
      (nativeShiftedFreeSheafBiproductIso 𝓑 w).hom =
    biproduct.matrix (fun i j => nativeShiftedFreeCoordinateSheafInclusion 𝓑 z i ≫
      nativeProjectiveDegreeZeroSheafMap 𝓑 (integerShiftedFreePiece 𝓑 z)
        (integerShiftedFreePiece 𝓑 w) (integerShiftedFreePiece_smul_homogeneous 𝓑 z)
        (integerShiftedFreePiece_smul_homogeneous 𝓑 w) c hh 0 ≫
      nativeShiftedFreeCoordinateSheafProjection 𝓑 w j) := by
  apply biproduct.hom_ext'
  intro i
  apply biproduct.hom_ext
  intro j
  simp only [← Category.assoc]
  erw [nativeShiftedFreeSheafBiproductIso_inclusion 𝓑 z i]
  simp only [Category.assoc]
  erw [nativeShiftedFreeSheafBiproductIso_projection 𝓑 w j]
  rw [biproduct.ι_matrix_assoc,biproduct.lift_π]
end Matrix
end LinearStudy
