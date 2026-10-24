module
public import Linear.IntegerGradedKernelGenerators
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
variable {K S M : Type*} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K M)

/-- Regrade the SAME actual module by D[k]_d=D_(d+k). -/
def integerGradingShift (k : ℤ) (d : ℤ) : Submodule K M := 𝒟 (d+k)

/-- The original homogeneous S-action respects the actual shifted pieces. -/
theorem integerGradingShift_smul_homogeneous
    (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
      ∀ x : M, x ∈ 𝒟 d → c • x ∈ 𝒟 ((n : ℤ)+d)) (k : ℤ)
    (n : ℕ) (d : ℤ) (c : S) (hc : c ∈ 𝓑 n) (x : M)
    (hx : x ∈ integerGradingShift 𝒟 k d) :
    c • x ∈ integerGradingShift 𝒟 k ((n : ℤ)+d) := by
  simpa only [integerGradingShift, add_assoc] using hD n (d+k) c hc x hx

/-- Reindexing by d -> d+k preserves the actual internal direct sum. -/
theorem integerGradingShift_isInternal [DirectSum.Decomposition 𝒟] (k : ℤ) :
    DirectSum.IsInternal (integerGradingShift 𝒟 k) := by
  have h := DirectSum.Decomposition.isInternal 𝒟
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact h.submodule_iSupIndep.comp (fun _ _ heq => add_right_cancel heq)
  · have hs : Function.Surjective (fun d : ℤ => d+k) :=
      fun d => ⟨d-k, sub_add_cancel d k⟩
    exact (hs.iSup_comp 𝒟).trans h.submodule_iSup_eq_top

/-- Construct the shifted decomposition; it is not supplied as a certificate. -/
@[instance_reducible] def integerGradingShiftDecomposition
    [DirectSum.Decomposition 𝒟] (k : ℤ) :
    DirectSum.Decomposition (integerGradingShift 𝒟 k) :=
  (integerGradingShift_isInternal 𝒟 k).chooseDecomposition
end LinearStudy
