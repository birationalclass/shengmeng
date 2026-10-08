module
/-
The homogeneous multiplication/projection step of mathlib PR 9819's
Hilbert--Serre argument, adapted to current Submodule-based internal gradings.
No Hilbert polynomial or dimension comparison is assumed.
-/
public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K A M : Type*} [Field K] [CommRing A] [Algebra K A]
variable [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
variable (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]
variable (ℳ : ℕ → Submodule K M) [DirectSum.Decomposition ℳ]
variable [SetLike.GradedSMul 𝒜 ℳ]

/-- The ACTUAL K-linear homogeneous component of the graded module. -/
def gradedModuleProjection (n : ℕ) : M →ₗ[K] M :=
  (ℳ n).subtype.comp <| (DFinsupp.lapply n).comp (DirectSum.decomposeLinearEquiv ℳ).toLinearMap

theorem gradedModuleProjection_apply (n : ℕ) (m : M) :
    gradedModuleProjection ℳ n m = (DirectSum.decompose ℳ m n : M) := rfl

theorem gradedModuleProjection_on_piece (n k : ℕ) (m : M) (hm : m ∈ ℳ k) :
    gradedModuleProjection ℳ n m = if n = k then m else 0 := by
  rw [gradedModuleProjection_apply]
  split_ifs with h
  · subst h
    exact DirectSum.decompose_of_mem_same ℳ hm
  · exact DirectSum.decompose_of_mem_ne ℳ hm (Ne.symm h)

/-- Multiplication by a degree-d element shifts the ACTUAL projections by d. -/
theorem gradedModuleProjection_smul_homogeneous (d n : ℕ) (a : A)
    (ha : a ∈ 𝒜 d) (m : M) :
    gradedModuleProjection ℳ n (a • m) =
      if d ≤ n then a • gradedModuleProjection ℳ (n - d) m else 0 := by
  induction m using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous k m =>
      rw [gradedModuleProjection_on_piece ℳ n (d + k) (a • (m : M))
        (SetLike.GradedSMul.smul_mem ha m.property)]
      by_cases hdn : d ≤ n
      · rw [if_pos hdn, gradedModuleProjection_on_piece ℳ (n - d) k m m.property]
        by_cases hnk : n = d + k
        · have hsub : n - d = k := by omega
          simp [hnk, hsub]
        · have hsub : n - d ≠ k := by omega
          simp [hnk, hsub]
      · have hnk : n ≠ d + k := by omega
        simp [hdn, hnk]
  | add m m' hm hm' =>
      rw [smul_add, map_add, hm, hm', map_add]
      split_ifs <;> simp [smul_add]

/-- The kernel of multiplication by a homogeneous scalar is homogeneous. -/
def gradedScalarKernel (d : ℕ) (a : A) (ha : a ∈ 𝒜 d) : HomogeneousSubmodule 𝒜 ℳ where
  toSubmodule := LinearMap.ker (LinearMap.lsmul A M a)
  is_homogeneous' := by
    intro n m hm
    change a • (DirectSum.decompose ℳ m n : M) = 0
    change a • m = 0 at hm
    have h := gradedModuleProjection_smul_homogeneous 𝒜 ℳ d (d + n) a ha m
    simpa [hm, gradedModuleProjection_apply] using h.symm

/-- The image of multiplication by a homogeneous scalar is homogeneous. -/
def gradedScalarImage (d : ℕ) (a : A) (ha : a ∈ 𝒜 d) : HomogeneousSubmodule 𝒜 ℳ where
  toSubmodule := LinearMap.range (LinearMap.lsmul A M a)
  is_homogeneous' := by
    intro n m hm
    obtain ⟨m, rfl⟩ := hm
    change (DirectSum.decompose ℳ (a • m) n : M) ∈
      LinearMap.range (LinearMap.lsmul A M a)
    rw [← gradedModuleProjection_apply,
      gradedModuleProjection_smul_homogeneous 𝒜 ℳ d n a ha m]
    split_ifs
    · exact ⟨gradedModuleProjection ℳ (n - d) m, rfl⟩
    · exact ⟨0, by simp⟩
end LinearStudy
