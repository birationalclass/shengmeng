module
public import Linear.NativeProjectiveRingIntegerPieces
public import Mathlib.LinearAlgebra.Pi
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K S ι : Type*} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- Integer projection lands in the actual integer ring piece. -/
theorem gradedIntegerProjection_mem_integerPiece (j : ℤ) (x : S) :
    gradedIntegerProjection 𝓑 j x ∈ nativeProjectiveRingIntegerPiece 𝓑 j := by
  unfold nativeProjectiveRingIntegerPiece
  by_cases hj : 0 ≤ j
  · rw [ite_eq_left hj]
    simp only [gradedIntegerProjection, ite_eq_left hj]
    exact (DirectSum.decompose 𝓑 x j.toNat).property
  · simp [gradedIntegerProjection, hj]

/-- Actual ring projections are the identity on the matching integer
piece and zero on all other integer pieces, including negative degrees. -/
theorem gradedIntegerProjection_on_integerPiece (i j : ℤ) (x : S)
    (hx : x ∈ nativeProjectiveRingIntegerPiece 𝓑 j) :
    gradedIntegerProjection 𝓑 i x = if i = j then x else 0 := by
  unfold nativeProjectiveRingIntegerPiece at hx
  by_cases hj : 0 ≤ j
  · rw [ite_eq_left hj] at hx
    rw [gradedIntegerProjection_on_piece 𝓑 i j.toNat x hx]
    have hcast : (j.toNat : ℤ) = j := by omega
    rw [hcast]
  · rw [ite_eq_right hj, Submodule.mem_bot] at hx
    subst x
    simp

variable (w : ι → ℤ)

/-- The actual finite free module with generator i placed in degree
w i; its degree j coefficients lie in the original ring degree j-w i. -/
def integerShiftedFreePiece (j : ℤ) : Submodule K (ι → S) :=
  Submodule.pi Set.univ (fun i => nativeProjectiveRingIntegerPiece 𝓑 (j - w i))

/-- The actual componentwise projection on a shifted free module. -/
def integerShiftedFreeProjection (j : ℤ) : (ι → S) →ₗ[K] (ι → S) :=
  LinearMap.pi fun i =>
    (gradedIntegerProjection 𝓑 (j - w i)).comp (LinearMap.proj i)

theorem integerShiftedFreeProjection_mem (j : ℤ) (f : ι → S) :
    integerShiftedFreeProjection 𝓑 w j f ∈ integerShiftedFreePiece 𝓑 w j := by
  intro i hi
  exact gradedIntegerProjection_mem_integerPiece 𝓑 (j - w i) (f i)

theorem integerShiftedFreeProjection_on_piece (j k : ℤ) (f : ι → S)
    (hf : f ∈ integerShiftedFreePiece 𝓑 w k) :
    integerShiftedFreeProjection 𝓑 w j f = if j = k then f else 0 := by
  ext i
  change gradedIntegerProjection 𝓑 (j - w i) (f i) = (if j = k then f else 0) i
  rw [gradedIntegerProjection_on_integerPiece 𝓑 (j - w i) (k - w i) (f i)
    (hf i (Set.mem_univ i))]
  have he : j - w i = k - w i ↔ j = k := by omega
  simp only [he]
  split_ifs <;> rfl

/-- The actual pointwise upper-ring scalar action respects the shifted
integer degrees. -/
theorem integerShiftedFreePiece_smul_homogeneous (n : ℕ) (j : ℤ)
    (b : S) (hb : b ∈ 𝓑 n) (f : ι → S)
    (hf : f ∈ integerShiftedFreePiece 𝓑 w j) :
    b • f ∈ integerShiftedFreePiece 𝓑 w ((n : ℤ) + j) := by
  intro i hi
  have h := nativeProjectiveRingIntegerPiece_graded 𝓑 n (j - w i) b hb (f i)
    (hf i (Set.mem_univ i))
  have he : (n : ℤ) + (j - w i) = (n : ℤ) + j - w i := by omega
  change b * f i ∈ nativeProjectiveRingIntegerPiece 𝓑 ((n : ℤ) + j - w i)
  simpa only [he, smul_eq_mul] using h

end LinearStudy
