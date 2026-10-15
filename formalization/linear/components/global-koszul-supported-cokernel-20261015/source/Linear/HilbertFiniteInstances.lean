module
/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang

Adapted from mathlib PR 9819 FiniteInstances.lean, commit
413e5b872a7c758e0eb91f99cb96d6a61c81f0a2. The monomial expansion
is replaced by the current adjoin induction API and canonical subalgebra actions.
-/
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Adjoin.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module A M]

theorem finiteAdjoin_isNoetherian [IsNoetherianRing R] (s : Finset A) :
    IsNoetherianRing (Algebra.adjoin R (s : Set A)) := by
  letI := Algebra.FiniteType.adjoin_of_finite (R := R) s.finite_toSet
  exact Algebra.FiniteType.isNoetherianRing R _

/-- If x annihilates M, every scalar from R[S,x] acts like a scalar from R[S]. -/
theorem adjoin_annihilator_scalar_representative (s : Set A) (x : A)
    (hx : ∀ m : M, x • m = 0) (a : A)
    (ha : a ∈ Algebra.adjoin R (insert x s)) :
    ∃ b ∈ Algebra.adjoin R s, ∀ m : M, a • m = b • m := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
      rcases ha with rfl | ha
      · exact ⟨0, (Algebra.adjoin R s).zero_mem, fun m => by simp [hx]⟩
      · exact ⟨a, Algebra.subset_adjoin ha, fun m => rfl⟩
  | algebraMap r =>
      exact ⟨algebraMap R A r, (Algebra.adjoin R s).algebraMap_mem r, fun m => rfl⟩
  | add a b ha hb h₁ h₂ =>
      obtain ⟨a', ha', h₁⟩ := h₁
      obtain ⟨b', hb', h₂⟩ := h₂
      exact ⟨a' + b', (Algebra.adjoin R s).add_mem ha' hb',
        fun m => by simp only [add_smul, h₁ m, h₂ m]⟩
  | mul a b ha hb h₁ h₂ =>
      obtain ⟨a', ha', h₁⟩ := h₁
      obtain ⟨b', hb', h₂⟩ := h₂
      exact ⟨a' * b', (Algebra.adjoin R s).mul_mem ha' hb',
        fun m => by simp only [mul_smul, h₂ m, h₁ (b' • m)]⟩

/-- Actual finite generators remain finite after deleting an annihilating scalar. -/
theorem adjoin_finiteModule_of_annihilator [Module.Finite A M]
    (s : Set A) (x : A) (hgen : Algebra.adjoin R (insert x s) = ⊤)
    (hx : ∀ m : M, x • m = 0) :
    Module.Finite (Algebra.adjoin R s) M := by
  obtain ⟨t, ht⟩ := (Module.Finite.fg_top (R := A) (M := M))
  apply Module.Finite.of_fg_top
  refine ⟨t, ?_⟩
  apply Submodule.eq_top_iff'.mpr
  intro m
  have hm : m ∈ Submodule.span A (t : Set M) := by rw [ht]; trivial
  induction hm using Submodule.span_induction with
  | mem m hm => exact Submodule.subset_span hm
  | zero => exact Submodule.zero_mem _
  | add a b ha hb h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
  | smul a m hm h =>
      obtain ⟨b, hb, hab⟩ := adjoin_annihilator_scalar_representative s x hx a
        (by rw [hgen]; trivial)
      rw [hab m]
      exact Submodule.smul_mem _ (⟨b, hb⟩ : Algebra.adjoin R s) h
end LinearStudy
