module
public import Linear.GradedIntegerProjector
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace LinearStudy
variable {K S D : Type*} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup D] [Module K D] [Module S D] [IsScalarTower K S D]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K D) [DirectSum.Decomposition 𝒟]

/-- The actual projection of an integer-graded module onto one degree. -/
def integerGradedModuleProjection (d : ℤ) : D →ₗ[K] D :=
  (𝒟 d).subtype.comp <| (DFinsupp.lapply d).comp (DirectSum.decomposeLinearEquiv 𝒟).toLinearMap

theorem integerGradedModuleProjection_on_piece (i j : ℤ) (x : D) (hx : x ∈ 𝒟 j) :
    integerGradedModuleProjection 𝒟 i x = if i=j then x else 0 := by
  change (DirectSum.decompose 𝒟 x i : D) = if i=j then x else 0
  split_ifs with h
  · subst h
    exact DirectSum.decompose_of_mem_same 𝒟 hx
  · exact DirectSum.decompose_of_mem_ne 𝒟 hx (Ne.symm h)

/-- An actual degree-k map commutes with projections after shifting the
integer source degree. This controls the image ideal on actual Proj charts. -/
theorem integerHomogeneousMap_projection
    (k : ℤ) (e : D →ₗ[S] S)
    (hh : ∀ d : ℤ, ∀ x : D, x ∈ 𝒟 d →
      e x = gradedIntegerProjection 𝓑 (d+k) (e x))
    (i : ℕ) (x : D) :
    e (integerGradedModuleProjection 𝒟 ((i : ℤ)-k) x) =
      gradedModuleProjection 𝓑 i (e x) := by
  induction x using DirectSum.Decomposition.inductionOn 𝒟 with
  | zero => simp
  | @homogeneous d x =>
    have hiff : (i : ℤ)-k=d ↔ (i : ℤ)=d+k := by omega
    rw [integerGradedModuleProjection_on_piece 𝒟 _ d x x.property]
    have hproj : gradedModuleProjection 𝓑 i (e x) =
        if (i : ℤ)=d+k then e x else 0 := by
      have ht : gradedIntegerProjection 𝓑 (i : ℤ) = gradedModuleProjection 𝓑 i := by
        simp [gradedIntegerProjection]
      rw [← ht,hh d x x.property,gradedIntegerProjection_projector]
    rw [hproj]
    simp only [hiff]
    split_ifs <;> simp
  | add x y hx hy => simpa only [map_add,hx,hy] using (map_add e _ _)

end LinearStudy
