module
public import Linear.NativeShiftedFreeSheafMatrixZero
public import Linear.NativeIntegerTwistDegreeTransport
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
variable {K S I J : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑] [DecidableEq I] [DecidableEq J]
variable (z : I → ℤ) (w : J → ℤ) (c : (I → S) →ₗ[S] (J → S))
variable (hh : ∀ d : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece 𝓑 z d →
  c x ∈ integerShiftedFreePiece 𝓑 w d)
attribute [local instance] nativeProjectiveAtPrimeModuleScalar

omit [DecidableEq J] in
include hh in
/-- The actual original entry lies in its nonnegative original ring piece;
this follows from the original map's grading, not an extra matrix input. -/
theorem integerShiftedFreeMapEntry_mem_nat (i : I) (j : J) (h : w j ≤ z i) :
    integerShiftedFreeMapEntry c i j ∈ 𝓑 (z i-w j).toNat := by
  have hm := integerShiftedFreeMapEntry_mem 𝓑 z w c hh i j
  unfold nativeProjectiveRingIntegerPiece at hm
  rw [ite_eq_left (sub_nonneg.mpr h)] at hm
  exact hm

/-- Original scalar multiplication by the actual nonnegative entry, followed
only by the equality of the two original integer twist degrees. -/
def nativeShiftedFreeSheafNonnegativeEntry (i : I) (j : J) (h : w j ≤ z i) :
    nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (-z i) ⟶
    nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (-w j) :=
  nativeProjectiveHomogeneousSMul 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
    (nativeProjectiveRingIntegerPiece_graded 𝓑) (integerShiftedFreeMapEntry c i j)
    (z i-w j).toNat (integerShiftedFreeMapEntry_mem_nat 𝓑 z w c hh i j h) (-z i) ≫
  nativeRingIntegerTwistDegreeCast 𝓑 (by omega)

omit [DecidableEq J] in
/-- The constructed scalar entry multiplies every original-prime value by
precisely the original relation-map entry on every original open. -/
theorem nativeShiftedFreeSheafNonnegativeEntry_value (i : I) (j : J) (h : w j ≤ z i)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (s : nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (-z i) U) (p : U.unop) :
    (((nativeShiftedFreeSheafNonnegativeEntry 𝓑 z w c hh i j h).val.app U) s).1 p =
      integerShiftedFreeMapEntry c i j • s.1 p := by
  have hd : -z i + ((z i-w j).toNat : ℤ) = -w j := by omega
  change (((nativeRingIntegerTwistDegreeCast 𝓑 hd).val.app U)
    (((nativeProjectiveHomogeneousSMul 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (integerShiftedFreeMapEntry c i j)
      (z i-w j).toNat (integerShiftedFreeMapEntry_mem_nat 𝓑 z w c hh i j h)
      (-z i)).val.app U) s)).1 p = _
  exact (nativeRingIntegerTwistDegreeCast_value 𝓑 hd U _ p).trans
    (nativeProjectiveHomogeneousSMul_section_value 𝓑
    (nativeProjectiveRingIntegerPiece 𝓑) (nativeProjectiveRingIntegerPiece_graded 𝓑)
    (integerShiftedFreeMapEntry c i j) (z i-w j).toNat
    (integerShiftedFreeMapEntry_mem_nat 𝓑 z w c hh i j h) (-z i) U s p)

/-- The actual coordinate component of the original sheafified relation
map equals original homogeneous multiplication, including the necessary
integer degree equality. It is not defined by this comparison. -/
theorem nativeShiftedFreeSheaf_matrixEntry_nonnegative (i : I) (j : J) (h : w j ≤ z i) :
    nativeShiftedFreeCoordinateSheafInclusion 𝓑 z i ≫
      nativeProjectiveDegreeZeroSheafMap 𝓑 (integerShiftedFreePiece 𝓑 z)
        (integerShiftedFreePiece 𝓑 w) (integerShiftedFreePiece_smul_homogeneous 𝓑 z)
        (integerShiftedFreePiece_smul_homogeneous 𝓑 w) c hh 0 ≫
      nativeShiftedFreeCoordinateSheafProjection 𝓑 w j =
    nativeShiftedFreeSheafNonnegativeEntry 𝓑 z w c hh i j h := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  funext p
  erw [nativeShiftedFreeSheaf_matrixEntry_value 𝓑 c z w hh i j U s p]
  exact (nativeShiftedFreeSheafNonnegativeEntry_value 𝓑 z w c hh i j h U s p).symm

end LinearStudy
