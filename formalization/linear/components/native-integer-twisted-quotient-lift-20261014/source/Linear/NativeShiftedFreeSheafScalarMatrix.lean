module
public import Linear.NativeShiftedFreeSheafBiproductMap
public import Linear.NativeShiftedFreeSheafScalarEntry
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
variable {K S I J : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [DecidableEq I] [DecidableEq J]
variable (z : I → ℤ) (w : J → ℤ) (c : (I → S) →ₗ[S] (J → S))
variable (hh : ∀ d : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece 𝓑 z d →
  c x ∈ integerShiftedFreePiece 𝓑 w d)

/-- Scalar matrix entry from the ACTUAL original free relation map.
Nonnegative degrees use original homogeneous multiplication; negative
degrees use the actual zero sheaf morphism. -/
def nativeShiftedFreeSheafScalarMatrixEntry (i : I) (j : J) :
    nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (-z i) ⟶
    nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (-w j) :=
  if h : w j ≤ z i then nativeShiftedFreeSheafNonnegativeEntry 𝓑 z w c hh i j h else 0

/-- Every original coordinate component equals its actual scalar matrix
entry, with its negative-degree zero derived from original homogeneity. -/
theorem nativeShiftedFreeSheaf_matrixEntry_scalar (i : I) (j : J) :
    nativeShiftedFreeCoordinateSheafInclusion 𝓑 z i ≫
      nativeProjectiveDegreeZeroSheafMap 𝓑 (integerShiftedFreePiece 𝓑 z)
        (integerShiftedFreePiece 𝓑 w) (integerShiftedFreePiece_smul_homogeneous 𝓑 z)
        (integerShiftedFreePiece_smul_homogeneous 𝓑 w) c hh 0 ≫
      nativeShiftedFreeCoordinateSheafProjection 𝓑 w j =
    nativeShiftedFreeSheafScalarMatrixEntry 𝓑 z w c hh i j := by
  by_cases h : w j ≤ z i
  · rw [nativeShiftedFreeSheafScalarMatrixEntry, dite_eq_left h]
    exact nativeShiftedFreeSheaf_matrixEntry_nonnegative 𝓑 z w c hh i j h
  · rw [nativeShiftedFreeSheafScalarMatrixEntry, dite_eq_right h]
    exact nativeShiftedFreeSheaf_matrixEntry_zero 𝓑 z w c hh i j (lt_of_not_ge h)

/-- The ACTUAL original sheafified degree-zero free relation map becomes
the matrix of ORIGINAL homogeneous scalar multiplication under the
constructed coordinate biproduct isomorphisms. No matrix identity,
entry multiplication or negative-degree vanishing is assumed. -/
theorem nativeShiftedFreeSheafMap_scalarMatrix [Fintype I] [Fintype J] :
    (nativeShiftedFreeSheafBiproductIso 𝓑 z).inv ≫
      nativeProjectiveDegreeZeroSheafMap 𝓑 (integerShiftedFreePiece 𝓑 z)
        (integerShiftedFreePiece 𝓑 w) (integerShiftedFreePiece_smul_homogeneous 𝓑 z)
        (integerShiftedFreePiece_smul_homogeneous 𝓑 w) c hh 0 ≫
      (nativeShiftedFreeSheafBiproductIso 𝓑 w).hom =
    biproduct.matrix (nativeShiftedFreeSheafScalarMatrixEntry 𝓑 z w c hh) := by
  rw [nativeShiftedFreeSheafMap_biproductMatrix]
  congr 1
  funext i j
  exact nativeShiftedFreeSheaf_matrixEntry_scalar 𝓑 z w c hh i j

end LinearStudy
