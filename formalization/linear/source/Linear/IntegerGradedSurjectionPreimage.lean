module
public import Linear.IntegerGradedModuleProjection
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace LinearStudy
variable {K S D E : Type*} [Field K] [Ring S]
variable [AddCommGroup D] [Module K D] [Module S D]
variable [AddCommGroup E] [Module K E] [Module S E]
variable (𝒟 : ℤ → Submodule K D) (ℰ : ℤ → Submodule K E)
variable [DirectSum.Decomposition 𝒟] [DirectSum.Decomposition ℰ]
variable (e : D →ₗ[S] E)
variable (hh : ∀ d : ℤ, ∀ x : D, x ∈ 𝒟 d → e x ∈ ℰ d)
include hh

/-- Degree-preserving maps between actual integer-graded modules
commute with the actual homogeneous projections. -/
theorem integerDegreeZeroMap_projection (d : ℤ) (x : D) :
    e (integerGradedModuleProjection 𝒟 d x) =
      integerGradedModuleProjection ℰ d (e x) := by
  induction x using DirectSum.Decomposition.inductionOn 𝒟 with
  | zero => simp
  | @homogeneous j x =>
    rw [integerGradedModuleProjection_on_piece 𝒟 d j x x.property,
      integerGradedModuleProjection_on_piece ℰ d j (e x) (hh j x x.property)]
    split_ifs <;> simp
  | add x y hx hy => simp only [map_add,hx,hy]

/-- Ordinary surjectivity of an actual degree-preserving map suffices:
projecting a preimage produces a preimage in the exact target degree. -/
theorem integerDegreeZeroSurjection_homogeneous_preimages
    (he : Function.Surjective e) :
    ∀ d : ℤ, ∀ ell : E, ell ∈ ℰ d →
      ∃ x : D, x ∈ 𝒟 d ∧ e x = ell := by
  intro d ell hell
  obtain ⟨x,hx⟩ := he ell
  refine ⟨integerGradedModuleProjection 𝒟 d x,?_,?_⟩
  · exact (DirectSum.decompose 𝒟 x d).property
  · rw [integerDegreeZeroMap_projection 𝒟 ℰ e hh,hx,
      integerGradedModuleProjection_on_piece ℰ d d ell hell]
    simp

end LinearStudy
