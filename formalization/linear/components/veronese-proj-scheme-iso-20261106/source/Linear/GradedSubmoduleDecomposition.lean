module
/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang

Adapted from PR 9819 Subgrading.lean at commit
413e5b872a7c758e0eb91f99cb96d6a61c81f0a2. Use current Submodule
projections and the internal-direct-sum criterion instead of filtered sums.
-/
public import Linear.GradedModuleProjection
public import Mathlib.Algebra.DirectSum.Module
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Classical
namespace LinearStudy
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
variable (ℳ : ℕ → Submodule K M) [DirectSum.Decomposition ℳ]
variable (p : Submodule K M) (hp : p.IsHomogeneous ℳ)

def gradedSubmodulePiece (n : ℕ) : Submodule K p := (ℳ n).comap p.subtype

def gradedSubmoduleProjection (n : ℕ) : p →ₗ[K] p where
  toFun m := ⟨gradedModuleProjection ℳ n (m : M),
    by simpa only [gradedModuleProjection_apply] using hp n m.property⟩
  map_add' := by intro a b; ext; exact map_add (gradedModuleProjection ℳ n) (a : M) (b : M)
  map_smul' := by intro a b; ext; exact map_smul (gradedModuleProjection ℳ n) a (b : M)

theorem gradedSubmoduleProjection_coe (n : ℕ) (m : p) :
    (gradedSubmoduleProjection ℳ p hp n m : M) = gradedModuleProjection ℳ n (m : M) := rfl

theorem gradedSubmoduleProjection_mem (n : ℕ) (m : p) :
    gradedSubmoduleProjection ℳ p hp n m ∈ gradedSubmodulePiece ℳ p n :=
  (DirectSum.decompose ℳ (m : M) n).property

theorem gradedSubmoduleProjection_on_piece (n k : ℕ) (m : p)
    (hm : m ∈ gradedSubmodulePiece ℳ p k) :
    gradedSubmoduleProjection ℳ p hp n m = if n = k then m else 0 := by
  apply Subtype.ext
  change gradedModuleProjection ℳ n (m : M) = ((if n = k then m else 0) : p)
  rw [gradedModuleProjection_on_piece ℳ n k (m : M) hm]
  split_ifs <;> rfl

include hp in
theorem gradedSubmodulePiece_independent : iSupIndep (gradedSubmodulePiece ℳ p) := by
  apply (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero (gradedSubmodulePiece ℳ p)).mpr
  intro s v hv hsum n hn
  have h := congrArg (gradedSubmoduleProjection ℳ p hp n) hsum
  simp only [map_sum, map_zero] at h
  have hterms : (∑ k ∈ s, gradedSubmoduleProjection ℳ p hp n (v k)) =
      ∑ k ∈ s, if n = k then v k else 0 :=
    Finset.sum_congr rfl (fun k hk =>
      gradedSubmoduleProjection_on_piece ℳ p hp n k (v k) (hv k hk))
  rw [hterms] at h
  simpa [hn] using h

theorem gradedSubmoduleProjection_sum (m : p) :
    ∑ n ∈ (DirectSum.decompose ℳ (m : M)).support,
      gradedSubmoduleProjection ℳ p hp n m = m := by
  apply Subtype.ext
  simp only [Submodule.coe_sum, gradedSubmoduleProjection_coe, gradedModuleProjection_apply]
  exact DirectSum.sum_support_decompose ℳ (m : M)

include hp in
theorem gradedSubmodulePiece_total : (⨆ n, gradedSubmodulePiece ℳ p n) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro m
  rw [← gradedSubmoduleProjection_sum ℳ p hp m]
  exact Submodule.sum_mem _ (fun n hn =>
    Submodule.mem_iSup_of_mem n (gradedSubmoduleProjection_mem ℳ p hp n m))

/-- The homogeneous submodule's ACTUAL internal decomposition, derived from p. -/
@[instance_reducible] def gradedSubmoduleDecomposition :
    DirectSum.Decomposition (gradedSubmodulePiece ℳ p) :=
  (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (gradedSubmodulePiece_independent ℳ p hp)
    (gradedSubmodulePiece_total ℳ p hp)).chooseDecomposition

theorem gradedSubmodulePiece_finite (n : ℕ) [Module.Finite K (ℳ n)] :
    Module.Finite K (gradedSubmodulePiece ℳ p n) := by
  let f : gradedSubmodulePiece ℳ p n →ₗ[K] ℳ n :=
    { toFun m := ⟨m.val.val, m.property⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  apply Module.Finite.of_injective f
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : ℳ n => (z : M)) h
end LinearStudy
