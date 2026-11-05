module
public import Linear.IntegerShiftedFreePieces
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
variable {K S I J : Type*} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [DecidableEq I] (z : I → ℤ) (w : J → ℤ)
variable (c : (I → S) →ₗ[S] (J → S))

/-- Entry (j,i) of the ACTUAL original relation map on shifted finite
free modules is obtained from its original coordinate basis vector. -/
def integerShiftedFreeMapEntry (i : I) (j : J) : S := c (Pi.single i 1) j

/-- A degree-zero original relation map has entries in precisely the
integer ring degree z_i-w_j. No independently supplied matrix is used. -/
theorem integerShiftedFreeMapEntry_mem
    (hh : ∀ d : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece 𝓑 z d →
      c x ∈ integerShiftedFreePiece 𝓑 w d) (i : I) (j : J) :
    integerShiftedFreeMapEntry c i j ∈ nativeProjectiveRingIntegerPiece 𝓑 (z i-w j) := by
  have hunit : (1:S) ∈ nativeProjectiveRingIntegerPiece 𝓑 0 := by
    simpa [nativeProjectiveRingIntegerPiece] using (SetLike.one_mem_graded 𝓑)
  have hs : Pi.single i (1:S) ∈ integerShiftedFreePiece 𝓑 z (z i) := by
    intro t ht
    by_cases he : t=i
    · subst t
      simp only [Pi.single_eq_same, sub_self]
      change (1:S) ∈ nativeProjectiveRingIntegerPiece 𝓑 0
      exact hunit
    · simp only [Pi.single_eq_of_ne he]
      exact (nativeProjectiveRingIntegerPiece 𝓑 (z i-z t)).zero_mem
  exact (hh (z i) _ hs) j (Set.mem_univ j)

/-- Negative-degree entries of an actual degree-zero free relation map
are zero, rather than omitted or replaced by an assumed zero entry. -/
theorem integerShiftedFreeMapEntry_eq_zero
    (hh : ∀ d : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece 𝓑 z d →
      c x ∈ integerShiftedFreePiece 𝓑 w d) (i : I) (j : J) (h : z i < w j) :
    integerShiftedFreeMapEntry c i j = 0 := by
  have hm := integerShiftedFreeMapEntry_mem 𝓑 z w c hh i j
  have hd : ¬ 0 ≤ z i-w j := by omega
  unfold nativeProjectiveRingIntegerPiece at hm
  rw [ite_eq_right hd] at hm
  simpa only [Submodule.mem_bot] using hm

/-- The original free relation map is recovered from these entries.
This uses mathlib's actual canonical-basis formula,not duality transport. -/
theorem integerShiftedFreeMap_apply [Fintype I] (x : I → S) (j : J) :
    c x j = ∑ i, x i * integerShiftedFreeMapEntry c i j := by
  have he : c x = ∑ i, x i • c (Pi.single i 1) := by
    calc
      c x = c (∑ i, Pi.single i (x i)) := congrArg c (LinearMap.sum_single_apply (fun _ : I => S) x).symm
      _ = ∑ i, c (Pi.single i (x i)) := by rw [map_sum]
      _ = ∑ i, x i • c (Pi.single i 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hs : Pi.single i (x i) = x i • Pi.single i (1:S) := by
          simpa only [smul_eq_mul, mul_one] using Pi.single_smul' i (x i) (1:S)
        rw [hs,map_smul]
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, integerShiftedFreeMapEntry]
    using congrArg (fun v : J → S => v j) he

end LinearStudy
