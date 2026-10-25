module
/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang

The empty-generator step of PR 9819 Hilbert--Serre, adapted to a fixed
base field and current Submodule gradings. A finite basis replaces the
old homogeneous-monomial expansion.
-/
public import Linear.GradedModuleProjection
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Adjoin.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
variable (ℳ : ℕ → Submodule K M) [DirectSum.Decomposition ℳ]

/-- An ACTUAL internal grading of a finite-dimensional module has bounded support. -/
theorem gradedModule_eventually_eq_bot [Module.Finite K M] :
    ∃ N : ℕ, ∀ n : ℕ, N < n → ℳ n = ⊥ := by
  classical
  let b := Module.finBasis K M
  let s : Finset ℕ := Finset.univ.biUnion fun i => (DirectSum.decompose ℳ (b i)).support
  refine ⟨s.sup id, fun n hn => ?_⟩
  have hns : n ∉ s := by
    intro h
    have hle : n ≤ s.sup id := Finset.le_sup (f := id) h
    omega
  have hp : gradedModuleProjection ℳ n = 0 := by
    apply b.ext
    intro i
    have hnot : n ∉ (DirectSum.decompose ℳ (b i)).support := by
      intro h
      exact hns (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩)
    have hzero : DirectSum.decompose ℳ (b i) n = 0 := by
      simpa only [DFinsupp.mem_support_iff, not_not] using hnot
    simp [gradedModuleProjection_apply, hzero]
  apply (Submodule.eq_bot_iff (ℳ n)).mpr
  intro m hm
  have h := LinearMap.congr_fun hp m
  simpa [gradedModuleProjection_on_piece ℳ n n m hm] using h

/-- The base case of Hilbert--Serre: an algebra with no generators over K
is K itself as a module, hence a finite module has bounded graded support. -/
theorem gradedModule_eventually_eq_bot_of_empty_generators
    {A : Type*} [CommRing A] [Algebra K A] [Module A M] [IsScalarTower K A M]
    [Module.Finite A M] (hgen : Algebra.adjoin K (∅ : Set A) = ⊤) :
    ∃ N : ℕ, ∀ n : ℕ, N < n → ℳ n = ⊥ := by
  have hsur : Function.Surjective (algebraMap K A) := by
    intro a
    have ha : a ∈ Algebra.adjoin K (∅ : Set A) := by rw [hgen]; trivial
    rw [Algebra.adjoin_empty] at ha
    exact Algebra.mem_bot.mp ha
  letI : Module.Finite K A := Module.Finite.of_surjective (Algebra.linearMap K A) hsur
  letI : Module.Finite K M := Module.Finite.trans A M
  exact gradedModule_eventually_eq_bot ℳ
end LinearStudy
