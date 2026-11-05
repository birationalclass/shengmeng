module
public import Linear.GradedModuleProjection
public import Mathlib.RingTheory.Finiteness.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K A M : Type*} [Field K] [CommRing A]
variable [AddCommGroup M] [Module K M] [Module A M]

/-- Finite module generators can be replaced by the finitely many ACTUAL
homogeneous components of those generators. No graded basis is assumed. -/
theorem finiteModule_exists_homogeneous_generators
    (ℳ : ℕ → Submodule K M) [DirectSum.Decomposition ℳ] [Module.Finite A M] :
    ∃ s : Finset M, Submodule.span A (s : Set M) = ⊤ ∧
      ∀ x ∈ s, ∃ d : ℕ, x ∈ ℳ d := by
  classical
  obtain ⟨F, hF⟩ := Module.Finite.fg_top (R := A) (M := M)
  let s : Finset M := F.biUnion fun x =>
    (DirectSum.decompose ℳ x).support.image fun d => (DirectSum.decompose ℳ x d : M)
  have hgen : Submodule.span A (F : Set M) ≤ Submodule.span A (s : Set M) := by
    apply Submodule.span_le.mpr
    intro x hx
    rw [← DirectSum.sum_support_decompose ℳ x]
    apply Submodule.sum_mem
    intro d hd
    apply Submodule.subset_span
    exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨d, hd, rfl⟩⟩
  refine ⟨s, le_antisymm le_top ?_, ?_⟩
  · rw [← hF]
    exact hgen
  · intro x hx
    obtain ⟨y, hy, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨d, (DirectSum.decompose ℳ y d).property⟩

end LinearStudy
