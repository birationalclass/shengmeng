module
public import Linear.NativeProjectiveRingIntegerPieces
public import Mathlib.Order.SupIndep
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- The original integer ring projection detects every actual integer
homogeneous piece, including the zero negative pieces. -/
theorem nativeProjectiveRingIntegerProjection_on_piece (d e : ℤ) (x : S)
    (hx : x ∈ nativeProjectiveRingIntegerPiece 𝓑 e) :
    gradedIntegerProjection 𝓑 d x = if d = e then x else 0 := by
  unfold nativeProjectiveRingIntegerPiece at hx
  by_cases he : 0 ≤ e
  · rw [ite_eq_left he] at hx
    rw [gradedIntegerProjection_on_piece 𝓑 d e.toNat x hx]
    rw [Int.toNat_of_nonneg he]
  · rw [ite_eq_right he,Submodule.mem_bot] at hx
    subst x
    simp

/-- The actual nonnegative ring grading remains independent when its
index set is extended to all integers by zero. -/
theorem nativeProjectiveRingIntegerPiece_independent :
    iSupIndep (nativeProjectiveRingIntegerPiece 𝓑) := by
  classical
  apply (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero
    (nativeProjectiveRingIntegerPiece 𝓑)).mpr
  intro s v hv hsum n hn
  have h := congrArg (gradedIntegerProjection 𝓑 n) hsum
  simp only [map_sum,map_zero] at h
  have hterms : (∑ k ∈ s, gradedIntegerProjection 𝓑 n (v k)) =
      ∑ k ∈ s, if n = k then v k else 0 :=
    Finset.sum_congr rfl (fun k hk =>
      nativeProjectiveRingIntegerProjection_on_piece 𝓑 n k (v k) (hv k hk))
  rw [hterms] at h
  simpa [hn] using h

/-- The integer pieces span the ORIGINAL ring, rather than a newly
supplied graded replacement. -/
theorem nativeProjectiveRingIntegerPiece_total :
    (⨆ d, nativeProjectiveRingIntegerPiece 𝓑 d) = ⊤ := by
  classical
  apply Submodule.eq_top_iff'.mpr
  intro x
  rw [← DirectSum.sum_support_decompose 𝓑 x]
  apply Submodule.sum_mem
  intro n _
  apply Submodule.mem_iSup_of_mem (n : ℤ)
  simpa only [nativeProjectiveRingIntegerPiece,Int.natCast_nonneg,ite_true,
    Int.toNat_natCast] using (DirectSum.decompose 𝓑 x n).property

/-- Construct the integer direct-sum decomposition of the ORIGINAL
graded ring. It is needed to apply actual finite-module section lifting. -/
@[instance_reducible] def nativeProjectiveRingIntegerDecomposition :
    DirectSum.Decomposition (nativeProjectiveRingIntegerPiece 𝓑) :=
  (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (nativeProjectiveRingIntegerPiece_independent 𝓑)
    (nativeProjectiveRingIntegerPiece_total 𝓑)).chooseDecomposition
end LinearStudy
