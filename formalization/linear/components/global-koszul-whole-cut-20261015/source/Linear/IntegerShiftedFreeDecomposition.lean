module
public import Linear.IntegerShiftedFreePieces
public import Mathlib.Order.SupIndep
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
open Classical
variable {K S ι : Type*} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [Fintype ι] [DecidableEq ι] (w : ι → ℤ)

/-- Different actual shifted degrees are linearly independent. -/
theorem integerShiftedFreePiece_independent : iSupIndep (integerShiftedFreePiece 𝓑 w) := by
  apply (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero (integerShiftedFreePiece 𝓑 w)).mpr
  intro s v hv hsum n hn
  have h := congrArg (integerShiftedFreeProjection 𝓑 w n) hsum
  simp only [map_sum, map_zero] at h
  have hterms : (∑ k ∈ s, integerShiftedFreeProjection 𝓑 w n (v k)) =
      ∑ k ∈ s, if n = k then v k else 0 :=
    Finset.sum_congr rfl (fun k hk =>
      integerShiftedFreeProjection_on_piece 𝓑 w n k (v k) (hv k hk))
  rw [hterms] at h
  simpa [hn] using h

/-- Decomposing each actual coefficient of the finite free module
proves that the actual shifted pieces span its original carrier. -/
theorem integerShiftedFreePiece_total : (⨆ j, integerShiftedFreePiece 𝓑 w j) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro f
  rw [← Finset.univ_sum_single f]
  apply Submodule.sum_mem
  intro i hi
  change (LinearMap.single (R := K) (φ := fun _ : ι => S) i) (f i) ∈ _
  rw [← DirectSum.sum_support_decompose 𝓑 (f i), map_sum]
  apply Submodule.sum_mem
  intro n hn
  apply Submodule.mem_iSup_of_mem ((n : ℤ) + w i)
  intro j hj
  by_cases h : j = i
  · subst j
    have hc : (DirectSum.decompose 𝓑 (f i) n : S) ∈
        nativeProjectiveRingIntegerPiece 𝓑 (n : ℤ) := by
      simpa only [nativeProjectiveRingIntegerPiece, Int.natCast_nonneg,
        ite_true, Int.toNat_natCast] using (DirectSum.decompose 𝓑 (f i) n).property
    simp
  · simp [h]

/-- Construct the actual integer grading of the original finite free
module with specified generator degrees. -/
@[instance_reducible] def integerShiftedFreeDecomposition :
    DirectSum.Decomposition (integerShiftedFreePiece 𝓑 w) :=
  (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (integerShiftedFreePiece_independent 𝓑 w)
    (integerShiftedFreePiece_total 𝓑 w)).chooseDecomposition

end LinearStudy
