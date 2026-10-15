module
public import Linear.ActualPresentationGradedDualKernel
public import Linear.IntegerGradedRingProduct
public import Linear.IntegerShiftedFreeMatrix
public import Mathlib.LinearAlgebra.StdBasis
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
variable {K S J : Type*} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [Fintype J] [DecidableEq J] (w : J → ℤ)

omit [Fintype J] in
/-- The actual original coordinate basis vector is homogeneous of its
original shifted-free weight. -/
theorem integerShiftedFree_single_one_mem (j : J) :
    Pi.single j (1:S) ∈ integerShiftedFreePiece 𝓑 w (w j) := by
  have hunit : (1:S) ∈ nativeProjectiveRingIntegerPiece 𝓑 0 := by
    simpa [nativeProjectiveRingIntegerPiece] using (SetLike.one_mem_graded 𝓑)
  intro t ht
  by_cases he : t=j
  · subst t
    simp only [Pi.single_eq_same,sub_self]
    exact hunit
  · simp only [Pi.single_eq_of_ne he]
    exact (nativeProjectiveRingIntegerPiece 𝓑 (w j-w t)).zero_mem

/-- The original free-module dual coordinates use mathlib's canonical
coordinate basis,not a duality or a chosen arbitrary comparison. -/
def integerShiftedFreeDualCoordinates : Module.Dual S (J → S) ≃ₗ[K] (J → S) :=
  (((Pi.basisFun S J).constr (M' := S) S).symm).restrictScalars K

theorem integerShiftedFreeDualCoordinates_apply (φ : Module.Dual S (J → S)) (j : J) :
    integerShiftedFreeDualCoordinates (K := K) φ j = φ (Pi.single j (1:S)) := by
  change φ ((Pi.basisFun S J) j) = _
  rw [Pi.basisFun_apply]

/-- Actual homogeneous polynomial coordinate tuple for a degree-d
functional on the original shifted-free module. Negative pieces are zero. -/
def integerShiftedFreeDualCoordinatePiece (d : ℤ) : Submodule K (J → S) :=
  Submodule.pi Set.univ (fun j => nativeProjectiveRingIntegerPiece 𝓑 (w j+d))

/-- Original S-linear Hom degree d is exactly the original basis
coordinate-degree condition,derived from actual grading and finite sums. -/
theorem integerShiftedFreeHomPiece_iff_coordinates (d : ℤ)
    (φ : Module.Dual S (J → S)) :
    φ ∈ integerGradedHomPiece 𝓑 (integerShiftedFreePiece 𝓑 w) d ↔
      integerShiftedFreeDualCoordinates (K := K) φ ∈ integerShiftedFreeDualCoordinatePiece 𝓑 w d := by
  constructor
  · intro hφ j hj
    change integerShiftedFreeDualCoordinates (K := K) φ j ∈
      nativeProjectiveRingIntegerPiece 𝓑 (w j+d)
    rw [integerShiftedFreeDualCoordinates_apply]
    exact hφ (w j) (Pi.single j 1) (integerShiftedFree_single_one_mem 𝓑 w j)
  · intro hφ t x hx
    have he : φ x = ∑ j, x j * integerShiftedFreeDualCoordinates (K := K) φ j := by
      simpa only [LinearMap.pi_apply,integerShiftedFreeMapEntry,integerShiftedFreeDualCoordinates_apply]
        using integerShiftedFreeMap_apply (LinearMap.pi (fun _ : Unit => φ)) x ()
    rw [he]
    apply Submodule.sum_mem
    intro j hj
    have hc := hx j (Set.mem_univ j)
    have hp := hφ j (Set.mem_univ j)
    have hm := nativeProjectiveRingIntegerPiece_mul_mem 𝓑 hc hp
    have hd : (t-w j)+(w j+d) = t+d := by omega
    simpa only [hd] using hm

/-- Canonical original homogeneous free Hom coordinates,restricted using
mathlib's actual submodule equivalence. No tuple comparison is assumed. -/
def integerShiftedFreeHomCoordinatesEquiv (d : ℤ) :
    integerGradedHomPiece 𝓑 (integerShiftedFreePiece 𝓑 w) d ≃ₗ[K]
      integerShiftedFreeDualCoordinatePiece 𝓑 w d :=
  (LinearEquiv.ofEq _ _ (by
    ext φ
    exact integerShiftedFreeHomPiece_iff_coordinates 𝓑 w d φ)).trans
      ((integerShiftedFreeDualCoordinates (K := K) (S := S) (J := J)).ofSubmodule'
        (integerShiftedFreeDualCoordinatePiece 𝓑 w d))

/-- The homogeneous coordinate comparison is still evaluation on the
original coordinate basis,including every zero negative-degree piece. -/
theorem integerShiftedFreeHomCoordinatesEquiv_apply (d : ℤ)
    (φ : integerGradedHomPiece 𝓑 (integerShiftedFreePiece 𝓑 w) d) (j : J) :
    (integerShiftedFreeHomCoordinatesEquiv 𝓑 w d φ).1 j = φ.1 (Pi.single j (1:S)) := by
  change integerShiftedFreeDualCoordinates (K := K) φ.1 j = _
  exact integerShiftedFreeDualCoordinates_apply φ.1 j

end LinearStudy
