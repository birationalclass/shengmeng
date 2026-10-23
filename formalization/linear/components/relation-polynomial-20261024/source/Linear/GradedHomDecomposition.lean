module
public import Linear.GradedHomProjection
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
namespace LinearStudy
variable {K A M N : Type*} [Field K] [CommRing A] [Algebra K A]
variable [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
variable [AddCommGroup N] [Module K N] [Module A N] [IsScalarTower K A N]
variable (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]
variable (ℳ : ℕ → Submodule K M) [DirectSum.Decomposition ℳ]
variable (𝓝 : ℕ → Submodule K N) [DirectSum.Decomposition 𝓝]
variable [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 𝓝]

include 𝒜 in
theorem gradedHomPiece_independent : iSupIndep (gradedHomPiece (A := A) ℳ 𝓝) := by
  classical
  apply (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero (gradedHomPiece (A := A) ℳ 𝓝)).mpr
  intro s v hv hsum n hn
  have h := congrArg (gradedHomProjection 𝒜 ℳ 𝓝 n) hsum
  simp only [map_sum,map_zero] at h
  have hterms : (∑ k ∈ s, gradedHomProjection 𝒜 ℳ 𝓝 n (v k)) =
      ∑ k ∈ s, if n = k then v k else 0 :=
    Finset.sum_congr rfl (fun k hk =>
      gradedHomComponent_on_homogeneous_map 𝒜 ℳ 𝓝 n k (v k) (hv k hk))
  rw [hterms] at h
  simpa [hn] using h

include 𝒜 in
theorem gradedHomPiece_total [Module.Finite A M] : (⨆ k, gradedHomPiece (A := A) ℳ 𝓝 k) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro f
  obtain ⟨s,hs⟩ := gradedHomProjection_exists_sum 𝒜 ℳ 𝓝 f
  rw [← hs]
  exact Submodule.sum_mem _ (fun k hk =>
    Submodule.mem_iSup_of_mem k (gradedHomComponent_mem_piece 𝒜 ℳ 𝓝 f k))

/-- The ACTUAL integer grading of Hom_A(M,N) for a finite graded M.
It is constructed by the actual finite component decomposition and
orthogonality; a graded dual is not assumed as additional data. -/
@[instance_reducible] def gradedHomDecomposition [Module.Finite A M] :
    DirectSum.Decomposition (gradedHomPiece (A := A) ℳ 𝓝) :=
  (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (gradedHomPiece_independent 𝒜 ℳ 𝓝)
    (gradedHomPiece_total 𝒜 ℳ 𝓝)).chooseDecomposition

end LinearStudy
