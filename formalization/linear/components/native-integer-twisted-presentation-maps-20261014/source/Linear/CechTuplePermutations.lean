/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.GroupTheory.Perm.Fin
public import Linear.ModuleOrderedBaseCech

/-!
# Alternating extension of ordered Cech cochains

Pure finite-tuple permutation signs and deleted-tuple injectivity lemmas,
used by the ordered support contraction. No whole foreign sheaf comparison is imported.
-/

/- Minimal reviewed adaptation from CBirkbeck/AINTLIB, commit ab1451487da02cd4483d0e2cdb2cc9e44bbbac17.
   Upstream: ForMathlib/SchemeModuleOrderedBaseCechAlternating.lean. Original4.1/4.2 and actual projective vanishing remain OPEN. -/
@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Category
  CategoryTheory.Limits CategoryTheory.Preadditive Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- The permutation relating the two faces obtained by deleting `k` and `l`. -/
def cechDeleteSwapFullPerm {n : ℕ} (k l : Fin (n + 2)) :
    Equiv.Perm (Fin (n + 2)) :=
  (k.cycleRange.symm.trans (Equiv.swap k l)).trans l.cycleRange

/-- The restriction of `cechDeleteSwapFullPerm` to the positive indices. -/
def cechDeleteSwapPerm {n : ℕ} (k l : Fin (n + 2)) :
    Equiv.Perm (Fin (n + 1)) :=
  (Equiv.Perm.decomposeFin (cechDeleteSwapFullPerm k l)).2

theorem cechDeleteSwapFullPerm_apply_zero {n : ℕ} (k l : Fin (n + 2)) :
    cechDeleteSwapFullPerm k l 0 = 0 := by
  simp [cechDeleteSwapFullPerm]

theorem cechDeleteSwapFullPerm_eq_decomposeFin {n : ℕ}
    (k l : Fin (n + 2)) :
    cechDeleteSwapFullPerm k l =
      Equiv.Perm.decomposeFin.symm (0, cechDeleteSwapPerm k l) := by
  apply Equiv.Perm.decomposeFin.injective
  apply Prod.ext
  · simpa [Equiv.Perm.decomposeFin] using
      cechDeleteSwapFullPerm_apply_zero k l
  · rfl

theorem cechDeleteSwapFullPerm_apply_succ {n : ℕ}
    (k l : Fin (n + 2)) (x : Fin (n + 1)) :
    cechDeleteSwapFullPerm k l x.succ = (cechDeleteSwapPerm k l x).succ := by
  rw [cechDeleteSwapFullPerm_eq_decomposeFin]
  simp

theorem succAbove_cechDeleteSwapPerm {n : ℕ}
    (k l : Fin (n + 2)) (x : Fin (n + 1)) :
    l.succAbove (cechDeleteSwapPerm k l x) =
      Equiv.swap k l (k.succAbove x) := by
  apply l.cycleRange.injective
  rw [Fin.cycleRange_succAbove]
  rw [← cechDeleteSwapFullPerm_apply_succ k l x]
  simp [cechDeleteSwapFullPerm]

theorem comp_succAbove_cechDeleteSwapPerm_of_eq {n : ℕ}
    {ι : Type*} (i : Fin (n + 2) → ι) (k l : Fin (n + 2))
    (hkl : i k = i l) :
    (i ∘ l.succAbove) ∘ cechDeleteSwapPerm k l =
      i ∘ k.succAbove := by
  funext x
  rw [Function.comp_apply, Function.comp_apply, Function.comp_apply,
    succAbove_cechDeleteSwapPerm]
  exact Equiv.apply_swap_eq_self hkl _

theorem cechDeleteSwapPerm_sign {n : ℕ}
    (k l : Fin (n + 2)) (hkl : k ≠ l) :
    (Equiv.Perm.sign (cechDeleteSwapPerm k l) : ℤ) =
      -((-1 : ℤ) ^ (k : ℕ) * (-1 : ℤ) ^ (l : ℕ)) := by
  have hsign := congrArg Equiv.Perm.sign
    (cechDeleteSwapFullPerm_eq_decomposeFin k l)
  simp only [Equiv.Perm.decomposeFin.symm_sign, if_pos, one_mul] at hsign
  rw [← hsign]
  simp [cechDeleteSwapFullPerm, Equiv.Perm.sign_trans,
    Equiv.Perm.sign_swap hkl, Units.val_mul, mul_comm]

/-- The permutation induced on a tuple after deleting `r` and applying `σ`. -/
def cechPermDeleteFull {n : ℕ} (σ : Equiv.Perm (Fin (n + 2)))
    (r : Fin (n + 2)) : Equiv.Perm (Fin (n + 2)) :=
  (r.cycleRange.symm.trans σ).trans (σ r).cycleRange

/-- The restriction of `cechPermDeleteFull` to the positive indices. -/
def cechPermDelete {n : ℕ} (σ : Equiv.Perm (Fin (n + 2)))
    (r : Fin (n + 2)) : Equiv.Perm (Fin (n + 1)) :=
  (Equiv.Perm.decomposeFin (cechPermDeleteFull σ r)).2

theorem cechPermDeleteFull_apply_zero {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (r : Fin (n + 2)) :
    cechPermDeleteFull σ r 0 = 0 := by
  simp [cechPermDeleteFull]

theorem cechPermDeleteFull_eq_decomposeFin {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (r : Fin (n + 2)) :
    cechPermDeleteFull σ r =
      Equiv.Perm.decomposeFin.symm (0, cechPermDelete σ r) := by
  apply Equiv.Perm.decomposeFin.injective
  apply Prod.ext
  · simpa [Equiv.Perm.decomposeFin] using
      cechPermDeleteFull_apply_zero σ r
  · rfl

theorem cechPermDeleteFull_apply_succ {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (r : Fin (n + 2))
    (x : Fin (n + 1)) :
    cechPermDeleteFull σ r x.succ = (cechPermDelete σ r x).succ := by
  rw [cechPermDeleteFull_eq_decomposeFin]
  simp

theorem succAbove_cechPermDelete {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (r : Fin (n + 2))
    (x : Fin (n + 1)) :
    (σ r).succAbove (cechPermDelete σ r x) = σ (r.succAbove x) := by
  apply (σ r).cycleRange.injective
  rw [Fin.cycleRange_succAbove]
  rw [← cechPermDeleteFull_apply_succ σ r x]
  simp [cechPermDeleteFull]

theorem cechPermDelete_sign {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (r : Fin (n + 2)) :
    (Equiv.Perm.sign (cechPermDelete σ r) : ℤ) =
      (-1 : ℤ) ^ (r : ℕ) * (Equiv.Perm.sign σ : ℤ) *
        (-1 : ℤ) ^ (σ r : ℕ) := by
  have hsign := congrArg Equiv.Perm.sign
    (cechPermDeleteFull_eq_decomposeFin σ r)
  simp only [Equiv.Perm.decomposeFin.symm_sign, if_pos, one_mul] at hsign
  rw [← hsign]
  simp [cechPermDeleteFull, Equiv.Perm.sign_trans, Units.val_mul,
    mul_comm, mul_left_comm]

theorem cechPermDelete_signed_coefficient {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (r : Fin (n + 2)) :
    (-1 : ℤ) ^ (r : ℕ) * (Equiv.Perm.sign (cechPermDelete σ r) : ℤ) =
      (Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ (σ r : ℕ) := by
  rw [cechPermDelete_sign]
  have hr : (-1 : ℤ) ^ (r : ℕ) * (-1 : ℤ) ^ (r : ℕ) = 1 := by
    rw [← pow_add, (Even.add_self (r : ℕ)).neg_one_pow]
  rw [← mul_assoc ((-1 : ℤ) ^ (r : ℕ))
      (((-1 : ℤ) ^ (r : ℕ)) * (Equiv.Perm.sign σ : ℤ))
      ((-1 : ℤ) ^ (σ r : ℕ)),
    ← mul_assoc ((-1 : ℤ) ^ (r : ℕ))
      ((-1 : ℤ) ^ (r : ℕ)) (Equiv.Perm.sign σ : ℤ),
    hr, one_mul]

theorem exists_eq_ne_of_not_injective
    {α β : Type*} (f : α → β) (hf : ¬ Function.Injective f) :
    ∃ a b, f a = f b ∧ a ≠ b := by
  by_contra h
  apply hf
  intro a b hab
  by_contra hne
  exact h ⟨a, b, hab, hne⟩

theorem exists_partner_of_delete_injective {n : ℕ}
    {ι : Type*} (i : Fin (n + 2) → ι) (hi : ¬ Function.Injective i)
    (k : Fin (n + 2)) (hk : Function.Injective (i ∘ k.succAbove)) :
    ∃ l, l ≠ k ∧ i l = i k := by
  obtain ⟨a, b, hab, hne⟩ := exists_eq_ne_of_not_injective i hi
  by_cases ha : a = k
  · subst a
    exact ⟨b, hne.symm, hab.symm⟩
  by_cases hb : b = k
  · subst b
    exact ⟨a, ha, hab⟩
  obtain ⟨a', ha'⟩ := Fin.exists_succAbove_eq ha
  obtain ⟨b', hb'⟩ := Fin.exists_succAbove_eq hb
  exfalso
  apply hne
  rw [← ha', ← hb']
  exact congrArg k.succAbove (hk (by simpa [ha', hb'] using hab))

theorem eq_partner_of_delete_injective {n : ℕ}
    {ι : Type*} (i : Fin (n + 2) → ι) (k l x : Fin (n + 2))
    (hk : Function.Injective (i ∘ k.succAbove))
    (hlk : l ≠ k) (hxk : x ≠ k) (hil : i l = i k) (hix : i x = i k) :
    x = l := by
  obtain ⟨x', hx'⟩ := Fin.exists_succAbove_eq hxk
  obtain ⟨l', hl'⟩ := Fin.exists_succAbove_eq hlk
  rw [← hx', ← hl']
  apply congrArg k.succAbove
  apply hk
  simp [hx', hl', hix, hil]

theorem delete_partner_injective {n : ℕ}
    {ι : Type*} (i : Fin (n + 2) → ι) (k l : Fin (n + 2))
    (hk : Function.Injective (i ∘ k.succAbove))
    (hlk : l ≠ k) (hil : i l = i k) :
    Function.Injective (i ∘ l.succAbove) := by
  intro a b hab
  apply Fin.succAbove_right_injective
  let x := l.succAbove a
  let y := l.succAbove b
  change x = y
  by_cases hxk : x = k
  · by_cases hyk : y = k
    · exact hxk.trans hyk.symm
    · have hyl : y = l := eq_partner_of_delete_injective
        i k l y hk hlk hyk hil (by simpa [x, y, hxk] using hab.symm)
      exact (l.succAbove_ne b hyl).elim
  · by_cases hyk : y = k
    · have hxl : x = l := eq_partner_of_delete_injective
        i k l x hk hlk hxk hil (by simpa [x, y, hyk] using hab)
      exact (l.succAbove_ne a hxl).elim
    · obtain ⟨a', ha'⟩ := Fin.exists_succAbove_eq hxk
      obtain ⟨b', hb'⟩ := Fin.exists_succAbove_eq hyk
      rw [← ha', ← hb']
      exact congrArg k.succAbove (hk (by simpa [x, y, ha', hb'] using hab))

theorem delete_not_injective_of_ne {n : ℕ}
    {ι : Type*} (i : Fin (n + 2) → ι) (k l m : Fin (n + 2))
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) (hil : i l = i k) :
    ¬ Function.Injective (i ∘ m.succAbove) := by
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hkm
  obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hlm
  intro hm
  apply hkl
  rw [← ha, ← hb]
  exact congrArg m.succAbove (hm (by simpa [ha, hb] using hil.symm))


end

end AlgebraicGeometry.Scheme.Modules
