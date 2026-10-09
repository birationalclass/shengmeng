module
public import Linear.IntegerShiftedFreeDecomposition
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
open Classical
variable {K S M ι : Type*} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M]
variable [Fintype ι] [DecidableEq ι]

/-- The actual upper-linear map from the original finite free module
to a chosen finite list of actual generators. -/
def integerShiftedFreeGeneratorMap (v : ι → M) : (ι → S) →ₗ[S] M where
  toFun f := ∑ i, f i • v i
  map_add' := by intro f g; simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by intro a f; simp [Finset.smul_sum, mul_smul]

theorem integerShiftedFreeGeneratorMap_single (v : ι → M) (i : ι) (a : S) :
    integerShiftedFreeGeneratorMap v (Pi.single i a) = a • v i := by
  simp [integerShiftedFreeGeneratorMap]

/-- An actual spanning family gives an ordinary surjection of the
actual finite free module, without a supplied surjection certificate. -/
theorem integerShiftedFreeGeneratorMap_surjective (v : ι → M)
    (hgen : Submodule.span S (Set.range v) = ⊤) :
    Function.Surjective (integerShiftedFreeGeneratorMap (S := S) v) := by
  apply LinearMap.range_eq_top.mp
  apply eq_top_iff.mpr
  rw [← hgen]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  refine ⟨Pi.single i 1, ?_⟩
  simp [integerShiftedFreeGeneratorMap_single]

/-- Placing actual homogeneous generators in their actual integer
degrees makes the original finite free generator map degree preserving. -/
theorem integerShiftedFreeGeneratorMap_homogeneous
    (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
    (𝒟 : ℤ → Submodule K M)
    (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
      ∀ x : M, x ∈ 𝒟 d → b • x ∈ 𝒟 ((n : ℤ) + d))
    (w : ι → ℤ) (v : ι → M) (hv : ∀ i, v i ∈ 𝒟 (w i)) :
    ∀ d : ℤ, ∀ f : ι → S, f ∈ integerShiftedFreePiece 𝓑 w d →
      integerShiftedFreeGeneratorMap v f ∈ 𝒟 d := by
  intro d f hf
  apply Submodule.sum_mem
  intro i hi
  have hc := hf i (Set.mem_univ i)
  change f i ∈ nativeProjectiveRingIntegerPiece 𝓑 (d - w i) at hc
  unfold nativeProjectiveRingIntegerPiece at hc
  by_cases hd : 0 ≤ d - w i
  · rw [ite_eq_left hd] at hc
    have he : ((d - w i).toNat : ℤ) + w i = d := by omega
    simpa only [he] using hD (d - w i).toNat (w i) (f i) hc (v i) (hv i)
  · rw [ite_eq_right hd, Submodule.mem_bot] at hc
    rw [hc, zero_smul]
    exact (𝒟 d).zero_mem

end LinearStudy
