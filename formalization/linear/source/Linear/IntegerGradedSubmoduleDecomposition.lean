module
/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang

Adapted from PR 9819 Subgrading.lean at commit
413e5b872a7c758e0eb91f99cb96d6a61c81f0a2. Extended to actual integer-indexed submodules. Use current Submodule
projections and the internal-direct-sum criterion instead of filtered sums.
-/
public import Linear.IntegerGradedModuleProjection
public import Mathlib.Algebra.DirectSum.Module
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Classical
namespace LinearStudy
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
variable (ℳ : ℤ → Submodule K M) [DirectSum.Decomposition ℳ]
variable (p : Submodule K M) (hp : p.IsHomogeneous ℳ)

/-- The actual integer projection evaluated on the original carrier. -/
theorem integerGradedModuleProjection_apply (n : ℤ) (m : M) :
    integerGradedModuleProjection ℳ n m = (DirectSum.decompose ℳ m n : M) := rfl

def integerGradedSubmodulePiece (n : ℤ) : Submodule K p := (ℳ n).comap p.subtype

def integerGradedSubmoduleProjection (n : ℤ) : p →ₗ[K] p where
  toFun m := ⟨integerGradedModuleProjection ℳ n (m : M),
    by simpa only [integerGradedModuleProjection_apply] using hp n m.property⟩
  map_add' := by intro a b; ext; exact map_add (integerGradedModuleProjection ℳ n) (a : M) (b : M)
  map_smul' := by intro a b; ext; exact map_smul (integerGradedModuleProjection ℳ n) a (b : M)

theorem integerGradedSubmoduleProjection_coe (n : ℤ) (m : p) :
    (integerGradedSubmoduleProjection ℳ p hp n m : M) = integerGradedModuleProjection ℳ n (m : M) := rfl

theorem integerGradedSubmoduleProjection_mem (n : ℤ) (m : p) :
    integerGradedSubmoduleProjection ℳ p hp n m ∈ integerGradedSubmodulePiece ℳ p n :=
  (DirectSum.decompose ℳ (m : M) n).property

theorem integerGradedSubmoduleProjection_on_piece (n k : ℤ) (m : p)
    (hm : m ∈ integerGradedSubmodulePiece ℳ p k) :
    integerGradedSubmoduleProjection ℳ p hp n m = if n = k then m else 0 := by
  apply Subtype.ext
  change integerGradedModuleProjection ℳ n (m : M) = ((if n = k then m else 0) : p)
  rw [integerGradedModuleProjection_on_piece ℳ n k (m : M) hm]
  split_ifs <;> rfl

include hp in
theorem integerGradedSubmodulePiece_independent : iSupIndep (integerGradedSubmodulePiece ℳ p) := by
  apply (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero (integerGradedSubmodulePiece ℳ p)).mpr
  intro s v hv hsum n hn
  have h := congrArg (integerGradedSubmoduleProjection ℳ p hp n) hsum
  simp only [map_sum, map_zero] at h
  have hterms : (∑ k ∈ s, integerGradedSubmoduleProjection ℳ p hp n (v k)) =
      ∑ k ∈ s, if n = k then v k else 0 :=
    Finset.sum_congr rfl (fun k hk =>
      integerGradedSubmoduleProjection_on_piece ℳ p hp n k (v k) (hv k hk))
  rw [hterms] at h
  simpa [hn] using h

theorem integerGradedSubmoduleProjection_sum (m : p) :
    ∑ n ∈ (DirectSum.decompose ℳ (m : M)).support,
      integerGradedSubmoduleProjection ℳ p hp n m = m := by
  apply Subtype.ext
  simp only [Submodule.coe_sum, integerGradedSubmoduleProjection_coe, integerGradedModuleProjection_apply]
  exact DirectSum.sum_support_decompose ℳ (m : M)

include hp in
theorem integerGradedSubmodulePiece_total : (⨆ n, integerGradedSubmodulePiece ℳ p n) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro m
  rw [← integerGradedSubmoduleProjection_sum ℳ p hp m]
  exact Submodule.sum_mem _ (fun n hn =>
    Submodule.mem_iSup_of_mem n (integerGradedSubmoduleProjection_mem ℳ p hp n m))

/-- The homogeneous submodule's ACTUAL internal decomposition, derived from p. -/
@[instance_reducible] def integerGradedSubmoduleDecomposition :
    DirectSum.Decomposition (integerGradedSubmodulePiece ℳ p) :=
  (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (integerGradedSubmodulePiece_independent ℳ p hp)
    (integerGradedSubmodulePiece_total ℳ p hp)).chooseDecomposition

end LinearStudy
