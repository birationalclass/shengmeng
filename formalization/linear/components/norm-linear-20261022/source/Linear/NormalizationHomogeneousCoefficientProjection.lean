module
public import Linear.GradedModuleHomogeneousGenerators
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
namespace LinearStudy
variable {K R S : Type*} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑]

/-- For the original graded normalization action, a homogeneous source
generator selects the matching homogeneous BASE coefficient. This is the
coefficient step needed to construct finite generators of the full chart. -/
theorem normalizationProjection_smul_source_homogeneous
    (d n : ℕ) (r : R) (b : S) (hb : b ∈ 𝓑 d) :
    gradedModuleProjection 𝓑 n (r • b) =
      if d ≤ n then gradedModuleProjection 𝒜 (n-d) r • b else 0 := by
  induction r using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous k r =>
      rw [gradedModuleProjection_on_piece 𝓑 n (k+d) ((r : R) • b)
        (SetLike.GradedSMul.smul_mem r.property hb)]
      by_cases hdn : d ≤ n
      · rw [if_pos hdn,gradedModuleProjection_on_piece 𝒜 (n-d) k r r.property]
        by_cases hnk : n = k+d
        · have hsub : n-d = k := by omega
          simp [hnk,hsub]
        · have hsub : n-d ≠ k := by omega
          simp [hnk,hsub]
      · have hnk : n ≠ k+d := by omega
        simp [hdn,hnk]
  | add r s hr hs =>
      rw [add_smul,map_add,hr,hs,map_add]
      split_ifs <;> simp [add_smul]

end LinearStudy
