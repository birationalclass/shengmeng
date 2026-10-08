module
/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang

Adapted from PR 9819 Subgrading.lean at commit
413e5b872a7c758e0eb91f99cb96d6a61c81f0a2. Current linear projections
descend through the ACTUAL homogeneous submodule quotient.
-/
public import Linear.GradedSubmoduleDecomposition
public import Mathlib.LinearAlgebra.Quotient.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Classical
namespace LinearStudy
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
variable (ℳ : ℕ → Submodule K M) [DirectSum.Decomposition ℳ]
variable (p : Submodule K M) (hp : p.IsHomogeneous ℳ)

def gradedQuotientPiece (n : ℕ) : Submodule K (M ⧸ p) := (ℳ n).map p.mkQ

def gradedQuotientProjection (n : ℕ) : (M ⧸ p) →ₗ[K] (M ⧸ p) :=
  p.liftQ (p.mkQ.comp (gradedModuleProjection ℳ n)) (by
    intro m hm
    change p.mkQ (gradedModuleProjection ℳ n m) = 0
    apply (Submodule.Quotient.mk_eq_zero p).mpr
    simpa only [gradedModuleProjection_apply] using hp n hm)

theorem gradedQuotientProjection_mk (n : ℕ) (m : M) :
    gradedQuotientProjection ℳ p hp n (p.mkQ m) =
      p.mkQ (gradedModuleProjection ℳ n m) := rfl

theorem gradedQuotientProjection_on_piece (n k : ℕ) (a : M ⧸ p)
    (ha : a ∈ gradedQuotientPiece ℳ p k) :
    gradedQuotientProjection ℳ p hp n a = if n = k then a else 0 := by
  obtain ⟨m, hm, rfl⟩ := ha
  rw [gradedQuotientProjection_mk, gradedModuleProjection_on_piece ℳ n k m hm]
  split_ifs <;> simp

theorem gradedQuotientProjection_mem (n : ℕ) (a : M ⧸ p) :
    gradedQuotientProjection ℳ p hp n a ∈ gradedQuotientPiece ℳ p n := by
  refine Quotient.inductionOn' a ?_
  intro m
  change gradedQuotientProjection ℳ p hp n (p.mkQ m) ∈ gradedQuotientPiece ℳ p n
  rw [gradedQuotientProjection_mk]
  exact ⟨gradedModuleProjection ℳ n m, (DirectSum.decompose ℳ m n).property, rfl⟩

theorem gradedQuotientProjection_sum (a : M ⧸ p) :
    ∃ s : Finset ℕ, ∑ n ∈ s, gradedQuotientProjection ℳ p hp n a = a := by
  refine Quotient.inductionOn' a ?_
  intro m
  refine ⟨(DirectSum.decompose ℳ m).support, ?_⟩
  change (∑ n ∈ (DirectSum.decompose ℳ m).support,
    gradedQuotientProjection ℳ p hp n (p.mkQ m)) = p.mkQ m
  have h : ∑ n ∈ (DirectSum.decompose ℳ m).support,
      gradedModuleProjection ℳ n m = m := DirectSum.sum_support_decompose ℳ m
  simpa only [map_sum, gradedQuotientProjection_mk] using congrArg p.mkQ h

include hp in
theorem gradedQuotientPiece_independent : iSupIndep (gradedQuotientPiece ℳ p) := by
  apply (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero (gradedQuotientPiece ℳ p)).mpr
  intro s v hv hsum n hn
  have h := congrArg (gradedQuotientProjection ℳ p hp n) hsum
  simp only [map_sum, map_zero] at h
  have hterms : (∑ k ∈ s, gradedQuotientProjection ℳ p hp n (v k)) =
      ∑ k ∈ s, if n = k then v k else 0 :=
    Finset.sum_congr rfl (fun k hk =>
      gradedQuotientProjection_on_piece ℳ p hp n k (v k) (hv k hk))
  rw [hterms] at h
  simpa [hn] using h

include hp in
theorem gradedQuotientPiece_total : (⨆ n, gradedQuotientPiece ℳ p n) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro m
  obtain ⟨s, h⟩ := gradedQuotientProjection_sum ℳ p hp m
  rw [← h]
  exact Submodule.sum_mem _ (fun n hn =>
    Submodule.mem_iSup_of_mem n (gradedQuotientProjection_mem ℳ p hp n m))

/-- The ACTUAL quotient's internal grading, derived from homogeneity of p. -/
@[instance_reducible] def gradedQuotientDecomposition :
    DirectSum.Decomposition (gradedQuotientPiece ℳ p) :=
  (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (gradedQuotientPiece_independent ℳ p hp)
    (gradedQuotientPiece_total ℳ p hp)).chooseDecomposition

theorem gradedQuotientPiece_finite (n : ℕ) [Module.Finite K (ℳ n)] :
    Module.Finite K (gradedQuotientPiece ℳ p n) := by
  have h : (ℳ n).FG := Module.Finite.iff_fg.mp inferInstance
  exact Module.Finite.of_fg (h.map p.mkQ)
end LinearStudy
