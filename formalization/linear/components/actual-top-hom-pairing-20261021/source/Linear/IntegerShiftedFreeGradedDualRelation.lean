module
public import Linear.IntegerShiftedFreeDualRelations
public import Mathlib.LinearAlgebra.Matrix.ToLin
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
variable {K S I J : Type*} [Field K] [CommRing S] [Algebra K S]
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (c : (I → S) →ₗ[S] (J → S))

/-- The ACTUAL transpose-entry multiplication matrix,constructed by
mathlib's original matrix-vector linear map,not by transporting c*. -/
def integerShiftedFreeDualRelationMatrix : (J → S) →ₗ[K] (I → S) :=
  (Matrix.mulVecLin (fun i j => integerShiftedFreeMapEntry c i j)).restrictScalars K

omit [Fintype I] [DecidableEq J] in
theorem integerShiftedFreeDualRelationMatrix_apply (x : J → S) (i : I) :
    integerShiftedFreeDualRelationMatrix (K := K) c x i =
      ∑ j, integerShiftedFreeMapEntry c i j * x j := by
  rfl

variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (z : I → ℤ) (w : J → ℤ)
variable (hh : ∀ t : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece 𝓑 z t →
  c x ∈ integerShiftedFreePiece 𝓑 w t)

omit [Fintype I] [DecidableEq J] in
include hh in
/-- Actual original entry degrees prove that the actual transpose matrix
preserves the original homogeneous Hom-coordinate degrees. -/
theorem integerShiftedFreeDualRelationMatrix_mapsPiece (d : ℤ) (x : J → S)
    (hx : x ∈ integerShiftedFreeDualCoordinatePiece 𝓑 w d) :
    integerShiftedFreeDualRelationMatrix (K := K) c x ∈ integerShiftedFreeDualCoordinatePiece 𝓑 z d := by
  intro i hi
  change (∑ j, integerShiftedFreeMapEntry c i j * x j) ∈
    nativeProjectiveRingIntegerPiece 𝓑 (z i+d)
  apply Submodule.sum_mem
  intro j hj
  have hp := integerShiftedFreeMapEntry_mem 𝓑 z w c hh i j
  have hc := hx j (Set.mem_univ j)
  have hm := nativeProjectiveRingIntegerPiece_mul_mem 𝓑 hp hc
  have hd : (z i-w j)+(w j+d) = z i+d := by omega
  simpa only [hd] using hm

/-- The actual original transpose polynomial matrix in Hom degree d,
restricted to the actual original homogeneous coordinate pieces. -/
def integerShiftedFreeDualDegreeRelationMatrix (d : ℤ) :
    integerShiftedFreeDualCoordinatePiece 𝓑 w d →ₗ[K]
      integerShiftedFreeDualCoordinatePiece 𝓑 z d :=
  ((integerShiftedFreeDualRelationMatrix (K := K) c).domRestrict
    (integerShiftedFreeDualCoordinatePiece 𝓑 w d)).codRestrict
      (integerShiftedFreeDualCoordinatePiece 𝓑 z d)
      (fun x => integerShiftedFreeDualRelationMatrix_mapsPiece c 𝓑 z w hh d x.1 x.property)

omit [Fintype I] [DecidableEq J] in
theorem integerShiftedFreeDualDegreeRelationMatrix_apply (d : ℤ)
    (x : integerShiftedFreeDualCoordinatePiece 𝓑 w d) (i : I) :
    (integerShiftedFreeDualDegreeRelationMatrix c 𝓑 z w hh d x).1 i =
      ∑ j, integerShiftedFreeMapEntry c i j * x.1 j := by
  rfl

/-- Precomposition with the ORIGINAL c on ACTUAL original homogeneous
S-linear Hom pieces. The grading condition is derived from original hh. -/
def integerShiftedFreeGradedDualRelation (d : ℤ) :
    integerGradedHomPiece 𝓑 (integerShiftedFreePiece 𝓑 w) d →ₗ[K]
      integerGradedHomPiece 𝓑 (integerShiftedFreePiece 𝓑 z) d :=
  ((c.dualMap.restrictScalars K).domRestrict
    (integerGradedHomPiece 𝓑 (integerShiftedFreePiece 𝓑 w) d)).codRestrict
      (integerGradedHomPiece 𝓑 (integerShiftedFreePiece 𝓑 z) d) (fun φ => by
        intro t x hx
        exact φ.property t (c x) (hh t x hx))

/-- Actual original homogeneous c* and actual transpose multiplication
commute with the canonical original homogeneous Hom coordinates. -/
theorem integerShiftedFreeGradedDualRelation_coordinates (d : ℤ)
    (φ : integerGradedHomPiece 𝓑 (integerShiftedFreePiece 𝓑 w) d) :
    integerShiftedFreeHomCoordinatesEquiv 𝓑 z d
      (integerShiftedFreeGradedDualRelation c 𝓑 z w hh d φ) =
    integerShiftedFreeDualDegreeRelationMatrix c 𝓑 z w hh d
      (integerShiftedFreeHomCoordinatesEquiv 𝓑 w d φ) := by
  apply Subtype.ext
  funext i
  change integerShiftedFreeDualCoordinates (K := K) (φ.1.comp c) i =
    ∑ j, integerShiftedFreeMapEntry c i j * integerShiftedFreeDualCoordinates (K := K) φ.1 j
  exact integerShiftedFreeDual_relation_coordinates c φ.1 i

end LinearStudy
