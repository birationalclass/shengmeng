/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
module

public import Linear.ProjectiveLaurentInitialExponent

/-!
# First-anchor Laurent naturality for projective Cech intersections

This file handles the exceptional first Cech face, where deleting the first coordinate changes the
affine chart anchor. It identifies restriction with the induced change of Laurent exponents.
-/

set_option backward.privateInPublic true

@[expose] public section

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory HomogeneousIdeal Opposite TopologicalSpace

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

local instance : DecidableEq σ := Classical.decEq σ

theorem coordinateProductPolynomial_first_anchor_factor
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    coordinateProductPolynomial (R := R) (fun l => (a.1 l).down) =
      X (a.1 1).down *
        (coordinateTailPolynomial (R := R)
          (fun l => ((a.delete 0).1 l).down) * X (a.1 0).down) := by
  rw [coordinateProductPolynomial_eq_delete_mul (R := R) a 0,
    coordinateProductPolynomial, mul_assoc]
  rfl

theorem coordinateTailPolynomial_eq_first_mul_delete_zero
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    coordinateTailPolynomial (R := R) (fun l => (a.1 l).down) =
      X (a.1 1).down * coordinateTailPolynomial (R := R)
        (fun l => ((a.delete 0).1 l).down) := by
  have h := coordinateProductPolynomial_eq_delete_mul (R := R) a 0
  rw [coordinateProductPolynomial, coordinateProductPolynomial] at h
  change X (a.1 0).down *
      coordinateTailPolynomial (R := R) (fun l => (a.1 l).down) =
    (X (a.1 1).down * coordinateTailPolynomial (R := R)
      (fun l => ((a.delete 0).1 l).down)) * X (a.1 0).down at h
  rw [mul_comm _ (X (a.1 0).down)] at h
  exact X_mul_cancel_left_iff.mp h

noncomputable def coordinateFirstDirectAwayMap
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    HomogeneousLocalization.Away
        (homogeneousSubmodule σ R) (X (a.1 1).down) →+*
      HomogeneousLocalization.Away
        (homogeneousSubmodule σ R)
        (coordinateProductPolynomial (R := R) (fun l => (a.1 l).down)) :=
  HomogeneousLocalization.awayMap
    (homogeneousSubmodule σ R)
    (SetLike.mul_mem_graded
      (coordinateTailPolynomial_mem (R := R)
        (fun l => ((a.delete 0).1 l).down))
      (X_mem_homogeneousSubmodule_one R (a.1 0).down))
    (coordinateProductPolynomial_first_anchor_factor (R := R) a)

noncomputable def coordinateTargetTailAwayMap
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    HomogeneousLocalization.Away
        (homogeneousSubmodule σ R) (X (a.1 0).down) →+*
      HomogeneousLocalization.Away
        (homogeneousSubmodule σ R)
        (coordinateProductPolynomial (R := R) (fun l => (a.1 l).down)) :=
  HomogeneousLocalization.awayMap
    (homogeneousSubmodule σ R)
    (coordinateTailPolynomial_mem (R := R) (fun l => (a.1 l).down)) rfl

theorem coordinateFirstDirectAwayMap_awayVar_val
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : {j : σ // j ≠ (a.1 1).down}) :
    (coordinateFirstDirectAwayMap (R := R) a
      (awayVar R (a.1 1).down j)).val =
      Localization.mk
        (X j.1 * (coordinateTailPolynomial (R := R)
          (fun l => ((a.delete 0).1 l).down) * X (a.1 0).down) ^ 1)
        (⟨coordinateProductPolynomial (R := R) (fun l => (a.1 l).down) ^ 1,
          1, rfl⟩ : Submonoid.powers
            (coordinateProductPolynomial (R := R) (fun l => (a.1 l).down))) := by
  rw [coordinateFirstDirectAwayMap, awayVar,
    HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.Away.val_mk]

theorem coordinateTargetTailAwayMap_awayVar_val
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : {j : σ // j ≠ (a.1 0).down}) :
    (coordinateTargetTailAwayMap (R := R) a
      (awayVar R (a.1 0).down j)).val =
      Localization.mk
        (X j.1 * coordinateTailPolynomial (R := R)
          (fun l => (a.1 l).down) ^ 1)
        (⟨coordinateProductPolynomial (R := R) (fun l => (a.1 l).down) ^ 1,
          1, rfl⟩ : Submonoid.powers
            (coordinateProductPolynomial (R := R) (fun l => (a.1 l).down))) := by
  change HomogeneousLocalization.val
      (HomogeneousLocalization.awayMap
        (f := X (a.1 0).down)
        (g := coordinateTailPolynomial (R := R) (fun l => (a.1 l).down))
        (x := coordinateProductPolynomial (R := R) (fun l => (a.1 l).down))
        (homogeneousSubmodule σ R)
        (coordinateTailPolynomial_mem (R := R) (fun l => (a.1 l).down))
        (show coordinateProductPolynomial (R := R) (fun l => (a.1 l).down) =
          X (a.1 0).down *
            coordinateTailPolynomial (R := R) (fun l => (a.1 l).down) from rfl)
        (HomogeneousLocalization.Away.mk
          (homogeneousSubmodule σ R)
          (X_mem_homogeneousSubmodule_one R (a.1 0).down) 1 (X j.1) _)) = _
  rw [HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.Away.val_mk]

theorem coordinateFirstAwayVar_anchor_mul_transition
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    coordinateFirstDirectAwayMap (R := R) a
        (awayVar R (a.1 1).down
          ⟨(a.1 0).down, (coordinateOpenCechFirstSecond_ne a).symm⟩) *
      coordinateTargetTailAwayMap (R := R) a
        (awayVar R (a.1 0).down
          ⟨(a.1 1).down, coordinateOpenCechFirstSecond_ne a⟩) = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one]
  rw [coordinateFirstDirectAwayMap_awayVar_val,
    coordinateTargetTailAwayMap_awayVar_val]
  rw [Localization.mk_mul, ← Localization.mk_one,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by
    simp only [pow_one, Submonoid.coe_mul, Submonoid.coe_one, one_mul]
    rw [coordinateProductPolynomial,
      coordinateTailPolynomial_eq_first_mul_delete_zero (R := R) a]
    ring⟩

theorem coordinateFirstAwayVar_mul_transition
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : {j : σ // j ≠ (a.1 1).down}) (hj0 : j.1 ≠ (a.1 0).down) :
    coordinateFirstDirectAwayMap (R := R) a
        (awayVar R (a.1 1).down j) *
      coordinateTargetTailAwayMap (R := R) a
        (awayVar R (a.1 0).down
          ⟨(a.1 1).down, coordinateOpenCechFirstSecond_ne a⟩) =
      coordinateTargetTailAwayMap (R := R) a
        (awayVar R (a.1 0).down ⟨j.1, hj0⟩) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul]
  rw [coordinateFirstDirectAwayMap_awayVar_val,
    coordinateTargetTailAwayMap_awayVar_val,
    coordinateTargetTailAwayMap_awayVar_val]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨1, by
    simp only [pow_one, Submonoid.coe_mul, Submonoid.coe_one, one_mul]
    rw [coordinateProductPolynomial,
      coordinateTailPolynomial_eq_first_mul_delete_zero (R := R) a]
    ring⟩

theorem coordinateTargetTailAwayMap_awayVar_laurent
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : {j : σ // j ≠ (a.1 0).down}) :
    laurentMonomialRingEquiv R
        (coordinateTailExponent (fun l => (a.1 l).down))
        (coordinateProductAwayRingEquiv (R := R) (fun l => (a.1 l).down)
          (coordinateTargetTailAwayMap (R := R) a
            (awayVar R (a.1 0).down j))) =
      AddMonoidAlgebra.single
        (laurentExponentAwayMap
          (coordinateTailExponent (fun l => (a.1 l).down))
          (Finsupp.single j 1)) 1 := by
  rw [show coordinateTargetTailAwayMap (R := R) a =
      HomogeneousLocalization.awayMap
        (f := X (a.1 0).down)
        (g := coordinateTailPolynomial (R := R) (fun l => (a.1 l).down))
        (x := coordinateProductPolynomial (R := R) (fun l => (a.1 l).down))
        (homogeneousSubmodule σ R)
        (coordinateTailPolynomial_mem (R := R) (fun l => (a.1 l).down)) rfl
      from rfl]
  rw [coordinateProductAwayLaurentRingEquiv_awayMap,
    chartRingEquiv_apply_awayVar]
  change AddMonoidAlgebra.mapDomain _
      (AddMonoidAlgebra.single (Finsupp.single j 1) 1) = _
  rw [AddMonoidAlgebra.mapDomain_single]
  rfl

theorem laurentExponentAwayMap_single_one_degree
    {τ : Type} (m : τ →₀ ℕ) (j : τ) :
    Finsupp.degree
        ((laurentExponentAwayMap m (Finsupp.single j 1) :
          laurentExponentSubmonoid m) : τ →₀ ℤ) = 1 := by
  have h :
      ((laurentExponentAwayMap m (Finsupp.single j 1) :
        laurentExponentSubmonoid m) : τ →₀ ℤ) = Finsupp.single j 1 := by
    ext i
    rw [laurentExponentAwayMap_apply]
    by_cases hi : i = j
    · subst i
      simp
    · simp [hi]
  rw [h, Finsupp.degree_single]

theorem coordinateFirstAnchorGenerator_global
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    coordinateLaurentExponentDeleteEmbedding a 0 1
        (coordinateLaurentExponentEquiv
          (fun l => ((a.delete 0).1 l).down) 1
          (laurentExponentAwayMap
            (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
            (Finsupp.single
              (⟨(a.1 0).down, (coordinateOpenCechFirstSecond_ne a).symm⟩ :
                {j : σ // j ≠ (a.1 1).down}) 1))) =
      coordinateLaurentExponentEquiv (fun l => (a.1 l).down) 1 0 := by
  apply Subtype.ext
  apply Subtype.ext
  ext i
  change (coordinateLaurentExponentEquiv
      (fun l => ((a.delete 0).1 l).down) 1
      (laurentExponentAwayMap
        (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
        (Finsupp.single
          (⟨(a.1 0).down, (coordinateOpenCechFirstSecond_ne a).symm⟩ :
            {j : σ // j ≠ (a.1 1).down}) 1))).1.1 i =
    (coordinateLaurentExponentEquiv (fun l => (a.1 l).down) 1
      (0 : laurentExponentSubmonoid
        (coordinateTailExponent (fun l => (a.1 l).down)))).1.1 i
  by_cases hi0 : i = (a.1 0).down
  · subst i
    rw [coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _
        (coordinateOpenCechFirstSecond_ne a).symm,
      coordinateLaurentExponentEquiv_apply_anchor,
      laurentExponentAwayMap_apply]
    let j0 : {j : σ // j ≠ (a.1 1).down} :=
      ⟨(a.1 0).down, (coordinateOpenCechFirstSecond_ne a).symm⟩
    change ((Finsupp.single j0 1 j0 : ℕ) : ℤ) = 1
    simp
  · by_cases hi1 : i = (a.1 1).down
    · subst i
      change (coordinateLaurentExponentEquiv
          (fun l => ((a.delete 0).1 l).down) 1
          (laurentExponentAwayMap
            (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
            (Finsupp.single
              (⟨(a.1 0).down, (coordinateOpenCechFirstSecond_ne a).symm⟩ :
                {j : σ // j ≠ (a.1 1).down}) 1))).1.1
            ((a.delete 0).1 0).down = _
      rw [coordinateLaurentExponentEquiv_apply_anchor,
        coordinateLaurentExponentEquiv_apply_of_ne
          (a := fun l => (a.1 l).down) (d := 1)
          (e := (0 : laurentExponentSubmonoid
            (coordinateTailExponent (fun l => (a.1 l).down))))
          (i := (a.1 1).down) hi0]
      let j0 : {j : σ // j ≠ (a.1 1).down} :=
        ⟨(a.1 0).down, (coordinateOpenCechFirstSecond_ne a).symm⟩
      change 1 - Finsupp.degree
          (laurentExponentAwayMap
            (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
            (Finsupp.single j0 1)).1 = 0
      have hdeg : Finsupp.degree
          (laurentExponentAwayMap
            (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
            (Finsupp.single j0 1)).1 = 1 :=
        laurentExponentAwayMap_single_one_degree
          (coordinateTailExponent (fun l => ((a.delete 0).1 l).down)) j0
      exact sub_eq_zero.mpr hdeg.symm
    · rw [coordinateLaurentExponentEquiv_apply_of_ne
          (a := fun l => ((a.delete 0).1 l).down) (d := 1)
          (e := laurentExponentAwayMap
            (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
            (Finsupp.single
              (⟨(a.1 0).down, (coordinateOpenCechFirstSecond_ne a).symm⟩ :
                {j : σ // j ≠ (a.1 1).down}) 1))
          (i := i) hi1,
        coordinateLaurentExponentEquiv_apply_of_ne
          (a := fun l => (a.1 l).down) (d := 1)
          (e := (0 : laurentExponentSubmonoid
            (coordinateTailExponent (fun l => (a.1 l).down))))
          (i := i) hi0,
        laurentExponentAwayMap_apply]
      let j0 : {j : σ // j ≠ (a.1 1).down} :=
        ⟨(a.1 0).down, (coordinateOpenCechFirstSecond_ne a).symm⟩
      have hij : (⟨i, hi1⟩ : {j : σ // j ≠ (a.1 1).down}) ≠ j0 := by
        intro h
        exact hi0 (congrArg Subtype.val h)
      change ((Finsupp.single j0 1 ⟨i, hi1⟩ : ℕ) : ℤ) = 0
      simp [hij]

theorem coordinateFirstGenerator_global
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : {j : σ // j ≠ (a.1 1).down}) (hj0 : j.1 ≠ (a.1 0).down) :
    coordinateLaurentExponentDeleteEmbedding a 0 1
        (coordinateLaurentExponentEquiv
          (fun l => ((a.delete 0).1 l).down) 1
          (laurentExponentAwayMap
            (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
            (Finsupp.single j 1))) =
      coordinateLaurentExponentEquiv (fun l => (a.1 l).down) 1
        (laurentExponentAwayMap
          (coordinateTailExponent (fun l => (a.1 l).down))
          (Finsupp.single
            (⟨j.1, hj0⟩ : {j : σ // j ≠ (a.1 0).down}) 1)) := by
  apply Subtype.ext
  apply Subtype.ext
  ext i
  change (coordinateLaurentExponentEquiv
      (fun l => ((a.delete 0).1 l).down) 1
      (laurentExponentAwayMap
        (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
        (Finsupp.single j 1))).1.1 i =
    (coordinateLaurentExponentEquiv (fun l => (a.1 l).down) 1
      (laurentExponentAwayMap
        (coordinateTailExponent (fun l => (a.1 l).down))
        (Finsupp.single
          (⟨j.1, hj0⟩ : {j : σ // j ≠ (a.1 0).down}) 1))).1.1 i
  by_cases hi1 : i = (a.1 1).down
  · subst i
    change (coordinateLaurentExponentEquiv
        (fun l => ((a.delete 0).1 l).down) 1
        (laurentExponentAwayMap
          (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
          (Finsupp.single j 1))).1.1 ((a.delete 0).1 0).down = _
    rw [coordinateLaurentExponentEquiv_apply_anchor,
      coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _
        (coordinateOpenCechFirstSecond_ne a)]
    have hdeg : Finsupp.degree
        (laurentExponentAwayMap
          (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
          (Finsupp.single j 1)).1 = 1 :=
      laurentExponentAwayMap_single_one_degree
        (coordinateTailExponent (fun l => ((a.delete 0).1 l).down)) j
    rw [hdeg, laurentExponentAwayMap_apply]
    have hne :
        (⟨(a.1 1).down, coordinateOpenCechFirstSecond_ne a⟩ :
          {j : σ // j ≠ (a.1 0).down}) ≠ ⟨j.1, hj0⟩ := by
      intro h
      exact j.2 (congrArg Subtype.val h).symm
    rw [Finsupp.single_eq_of_ne hne]
    norm_num
  · by_cases hi0 : i = (a.1 0).down
    · subst i
      rw [coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _
          (coordinateOpenCechFirstSecond_ne a).symm,
        coordinateLaurentExponentEquiv_apply_anchor,
        laurentExponentAwayMap_apply]
      have hdeg : Finsupp.degree
          (laurentExponentAwayMap
            (coordinateTailExponent (fun l => (a.1 l).down))
            (Finsupp.single
              (⟨j.1, hj0⟩ : {j : σ // j ≠ (a.1 0).down}) 1)).1 = 1 :=
        laurentExponentAwayMap_single_one_degree
          (coordinateTailExponent (fun l => (a.1 l).down)) ⟨j.1, hj0⟩
      rw [hdeg]
      have hne :
          (⟨(a.1 0).down, (coordinateOpenCechFirstSecond_ne a).symm⟩ :
            {j : σ // j ≠ (a.1 1).down}) ≠ j := by
        intro h
        exact hj0 (congrArg Subtype.val h).symm
      let x : {j : σ // j ≠ (a.1 1).down} :=
        ⟨(a.1 0).down, (coordinateOpenCechFirstSecond_ne a).symm⟩
      have hx : (Finsupp.single j 1 :
          {j : σ // j ≠ (a.1 1).down} →₀ ℕ) x = 0 :=
        Finsupp.single_eq_of_ne hne
      change (((Finsupp.single j 1 :
        {j : σ // j ≠ (a.1 1).down} →₀ ℕ) x : ℕ) : ℤ) = 0
      exact congrArg (fun z : ℕ => (z : ℤ)) hx
    · rw [coordinateLaurentExponentEquiv_apply_of_ne
          (a := fun l => ((a.delete 0).1 l).down) (d := 1)
          (e := laurentExponentAwayMap
            (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
            (Finsupp.single j 1)) (i := i) hi1,
        coordinateLaurentExponentEquiv_apply_of_ne
          (a := fun l => (a.1 l).down) (d := 1)
          (e := laurentExponentAwayMap
            (coordinateTailExponent (fun l => (a.1 l).down))
            (Finsupp.single
              (⟨j.1, hj0⟩ : {j : σ // j ≠ (a.1 0).down}) 1))
          (i := i) hi0,
        laurentExponentAwayMap_apply, laurentExponentAwayMap_apply]
      by_cases hij : i = j.1
      · subst i
        change ((Finsupp.single j 1 j : ℕ) : ℤ) =
          ((Finsupp.single (⟨j.1, hj0⟩ :
            {j : σ // j ≠ (a.1 0).down}) 1 ⟨j.1, hj0⟩ : ℕ) : ℤ)
        rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
      · have hsource : (⟨i, hi1⟩ : {j : σ // j ≠ (a.1 1).down}) ≠ j := by
          intro h
          exact hij (congrArg Subtype.val h)
        have htarget :
            (⟨i, hi0⟩ : {j : σ // j ≠ (a.1 0).down}) ≠ ⟨j.1, hj0⟩ := by
          intro h
          exact hij (congrArg Subtype.val h)
        let xsource : {j : σ // j ≠ (a.1 1).down} := ⟨i, hi1⟩
        let xtarget : {j : σ // j ≠ (a.1 0).down} := ⟨i, hi0⟩
        have hs : (Finsupp.single j 1 :
            {j : σ // j ≠ (a.1 1).down} →₀ ℕ) xsource = 0 :=
          Finsupp.single_eq_of_ne hsource
        have ht : (Finsupp.single (⟨j.1, hj0⟩ :
            {j : σ // j ≠ (a.1 0).down}) 1 :
            {j : σ // j ≠ (a.1 0).down} →₀ ℕ) xtarget = 0 :=
          Finsupp.single_eq_of_ne htarget
        change (((Finsupp.single j 1 :
            {j : σ // j ≠ (a.1 1).down} →₀ ℕ) xsource : ℕ) : ℤ) =
          (((Finsupp.single (⟨j.1, hj0⟩ :
            {j : σ // j ≠ (a.1 0).down}) 1 :
            {j : σ // j ≠ (a.1 0).down} →₀ ℕ) xtarget : ℕ) : ℤ)
        exact congrArg (fun z : ℕ => (z : ℤ)) (hs.trans ht.symm)

theorem coordinateFirstAnchorExponent_add_transition
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    coordinateLaurentExponentDeleteZeroAddMonoidHom a
        (laurentExponentAwayMap
          (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
          (Finsupp.single
            (⟨(a.1 0).down, (coordinateOpenCechFirstSecond_ne a).symm⟩ :
              {j : σ // j ≠ (a.1 1).down}) 1)) +
      coordinateOpenCechFirstTransitionExponent (n := n) a 1 = 0 := by
  apply (coordinateLaurentExponentEquiv (fun l => (a.1 l).down) 1).injective
  rw [coordinateLaurentExponentEquiv_delete_zero_add_transition]
  exact coordinateFirstAnchorGenerator_global a

theorem coordinateFirstExponent_add_transition
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : {j : σ // j ≠ (a.1 1).down}) (hj0 : j.1 ≠ (a.1 0).down) :
    coordinateLaurentExponentDeleteZeroAddMonoidHom a
        (laurentExponentAwayMap
          (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
          (Finsupp.single j 1)) +
      coordinateOpenCechFirstTransitionExponent (n := n) a 1 =
        laurentExponentAwayMap
          (coordinateTailExponent (fun l => (a.1 l).down))
          (Finsupp.single
            (⟨j.1, hj0⟩ : {j : σ // j ≠ (a.1 0).down}) 1) := by
  apply (coordinateLaurentExponentEquiv (fun l => (a.1 l).down) 1).injective
  rw [coordinateLaurentExponentEquiv_delete_zero_add_transition]
  exact coordinateFirstGenerator_global a j hj0

theorem coordinateFirstTransitionExponent_one
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    laurentExponentAwayMap
        (coordinateTailExponent (fun l => (a.1 l).down))
        (Finsupp.single
          (⟨(a.1 1).down, coordinateOpenCechFirstSecond_ne a⟩ :
            {j : σ // j ≠ (a.1 0).down}) 1) =
      coordinateOpenCechFirstTransitionExponent (n := n) a 1 := by
  apply Subtype.ext
  ext i
  rw [laurentExponentAwayMap_apply]
  let j1 : {j : σ // j ≠ (a.1 0).down} :=
    ⟨(a.1 1).down, coordinateOpenCechFirstSecond_ne a⟩
  change ((Finsupp.single j1 1 i : ℕ) : ℤ) = Finsupp.single j1 1 i
  by_cases hi : i = j1
  · subst i
    simp
  · simp [hi]


end
end MvPolynomial
