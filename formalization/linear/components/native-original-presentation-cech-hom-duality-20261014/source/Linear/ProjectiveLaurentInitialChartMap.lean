/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
module

public import Linear.ProjectiveLaurentInitialGenerators

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

theorem coordinateFirstDirectAwayMap_awayVar_laurent
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : {j : σ // j ≠ (a.1 1).down}) :
    laurentMonomialRingEquiv R
        (coordinateTailExponent (fun l => (a.1 l).down))
        (coordinateProductAwayRingEquiv (R := R) (fun l => (a.1 l).down)
          (coordinateFirstDirectAwayMap (R := R) a
            (awayVar R (a.1 1).down j))) =
      AddMonoidAlgebra.single
        (coordinateLaurentExponentDeleteZeroAddMonoidHom a
          (laurentExponentAwayMap
            (coordinateTailExponent (fun l => ((a.delete 0).1 l).down))
            (Finsupp.single j 1))) 1 := by
  let E : HomogeneousLocalization.Away
        (homogeneousSubmodule σ R)
        (coordinateProductPolynomial (R := R) (fun l => (a.1 l).down)) ≃+*
      AddMonoidAlgebra R
        (laurentExponentSubmonoid
          (coordinateTailExponent (fun l => (a.1 l).down))) :=
    (coordinateProductAwayRingEquiv (R := R) (fun l => (a.1 l).down)).trans
      (laurentMonomialRingEquiv R
        (coordinateTailExponent (fun l => (a.1 l).down)))
  let j1 : {j : σ // j ≠ (a.1 0).down} :=
    ⟨(a.1 1).down, coordinateOpenCechFirstSecond_ne a⟩
  let t := coordinateTargetTailAwayMap (R := R) a
    (awayVar R (a.1 0).down j1)
  change E (coordinateFirstDirectAwayMap (R := R) a
      (awayVar R (a.1 1).down j)) = _
  have ht : E t = AddMonoidAlgebra.single
      (coordinateOpenCechFirstTransitionExponent (n := n) a 1) 1 := by
    change laurentMonomialRingEquiv R
        (coordinateTailExponent (fun l => (a.1 l).down))
        (coordinateProductAwayRingEquiv (R := R) (fun l => (a.1 l).down)
          (coordinateTargetTailAwayMap (R := R) a
            (awayVar R (a.1 0).down j1))) = _
    rw [coordinateTargetTailAwayMap_awayVar_laurent,
      coordinateFirstTransitionExponent_one]
  have htUnit : IsUnit (E t) := by
    let j0 : {j : σ // j ≠ (a.1 1).down} :=
      ⟨(a.1 0).down, (coordinateOpenCechFirstSecond_ne a).symm⟩
    have hrel := congrArg E
      (coordinateFirstAwayVar_anchor_mul_transition (R := R) a)
    change E (coordinateFirstDirectAwayMap (R := R) a
        (awayVar R (a.1 1).down j0) * t) = E 1 at hrel
    rw [map_mul, map_one] at hrel
    exact isUnit_iff_exists_inv.mpr
      ⟨E (coordinateFirstDirectAwayMap (R := R) a
        (awayVar R (a.1 1).down j0)), (mul_comm _ _).trans hrel⟩
  refine htUnit.mul_right_cancel ?_
  by_cases hj0 : j.1 = (a.1 0).down
  · have hj : j =
        (⟨(a.1 0).down, (coordinateOpenCechFirstSecond_ne a).symm⟩ :
          {j : σ // j ≠ (a.1 1).down}) := Subtype.ext hj0
    subst j
    rw [← map_mul,
      coordinateFirstAwayVar_anchor_mul_transition (R := R) a,
      map_one, ht, AddMonoidAlgebra.single_mul_single,
      coordinateFirstAnchorExponent_add_transition, mul_one]
    rfl
  · let jt : {j : σ // j ≠ (a.1 0).down} := ⟨j.1, hj0⟩
    rw [← map_mul,
      coordinateFirstAwayVar_mul_transition (R := R) a j hj0]
    change E (coordinateTargetTailAwayMap (R := R) a
        (awayVar R (a.1 0).down jt)) = _
    rw [show E (coordinateTargetTailAwayMap (R := R) a
          (awayVar R (a.1 0).down jt)) =
        AddMonoidAlgebra.single
          (laurentExponentAwayMap
            (coordinateTailExponent (fun l => (a.1 l).down))
            (Finsupp.single jt 1)) 1 by
          exact coordinateTargetTailAwayMap_awayVar_laurent
            (R := R) a jt]
    rw [ht, AddMonoidAlgebra.single_mul_single,
      coordinateFirstExponent_add_transition a j hj0, mul_one]

theorem chartRingEquiv_symm_X
    (i : σ) (j : {j : σ // j ≠ i}) :
    (chartRingEquiv R i).symm (X j) = awayVar R i j := by
  apply (chartRingEquiv R i).injective
  rw [RingEquiv.apply_symm_apply, chartRingEquiv_apply_awayVar]

theorem chartRingEquiv_symm_C (i : σ) (r : R) :
    (chartRingEquiv R i).symm (C r) =
      algebraMap R
        (HomogeneousLocalization.Away
          (homogeneousSubmodule σ R) (X i : MvPolynomial σ R)) r := by
  apply (chartRingEquiv R i).injective
  rw [RingEquiv.apply_symm_apply, chartRingEquiv_algebraMap]

theorem coordinateFirstDirectAwayMap_algebraMap
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (r : R) :
    coordinateFirstDirectAwayMap (R := R) a
        (algebraMap R
          (HomogeneousLocalization.Away
            (homogeneousSubmodule σ R) (X (a.1 1).down)) r) =
      algebraMap R
        (HomogeneousLocalization.Away
          (homogeneousSubmodule σ R)
          (coordinateProductPolynomial (R := R) (fun l => (a.1 l).down))) r := by
  change HomogeneousLocalization.awayMap
      (homogeneousSubmodule σ R)
      (SetLike.mul_mem_graded
        (coordinateTailPolynomial_mem (R := R)
          (fun l => ((a.delete 0).1 l).down))
        (X_mem_homogeneousSubmodule_one R (a.1 0).down))
      (coordinateProductPolynomial_first_anchor_factor (R := R) a)
      (HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule σ R)
        (Submonoid.powers (X (a.1 1).down))
        (algebraMap R (homogeneousSubmodule σ R 0) r)) =
    HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule σ R)
      (Submonoid.powers
        (coordinateProductPolynomial (R := R) (fun l => (a.1 l).down)))
      (algebraMap R (homogeneousSubmodule σ R 0) r)
  exact HomogeneousLocalization.awayMap_fromZeroRingHom
    (homogeneousSubmodule σ R)
    (SetLike.mul_mem_graded
      (coordinateTailPolynomial_mem (R := R)
        (fun l => ((a.delete 0).1 l).down))
      (X_mem_homogeneousSubmodule_one R (a.1 0).down))
    (coordinateProductPolynomial_first_anchor_factor (R := R) a)
    (algebraMap R (homogeneousSubmodule σ R 0) r)

noncomputable def coordinateFirstDirectLaurentRingHom
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :=
  (laurentMonomialRingEquiv R
        (coordinateTailExponent (fun l => (a.1 l).down))).toRingHom.comp
        ((coordinateProductAwayRingEquiv (R := R)
          (fun l => (a.1 l).down)).toRingHom.comp
          (coordinateFirstDirectAwayMap (R := R) a))

noncomputable def coordinateFirstTargetLaurentRingHom
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :=
  (AddMonoidAlgebra.mapDomainRingHom R
        (coordinateLaurentExponentDeleteZeroAddMonoidHom a)).comp
        ((AddMonoidAlgebra.mapDomainRingHom R
          (laurentExponentAwayMap
            (coordinateTailExponent
              (fun l => ((a.delete 0).1 l).down))).toAddMonoidHom).comp
          (chartRingEquiv R (a.1 1).down).toRingHom)

theorem coordinateFirstDirectAwayMap_laurent_C_left
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (r : R) :
    coordinateFirstDirectLaurentRingHom (R := R) a
        ((chartRingEquiv R (a.1 1).down).symm (C r)) =
      AddMonoidAlgebra.single 0 r := by
  change laurentMonomialRingEquiv R
      (coordinateTailExponent (fun l => (a.1 l).down))
      (coordinateProductAwayRingEquiv (R := R) (fun l => (a.1 l).down)
        (coordinateFirstDirectAwayMap (R := R) a
          ((chartRingEquiv R (a.1 1).down).symm (C r)))) = _
  rw [chartRingEquiv_symm_C,
    coordinateFirstDirectAwayMap_algebraMap,
    coordinateProductAwayRingEquiv_algebraMap,
    laurentMonomialRingEquiv_algebraMap_coeff]
  change AddMonoidAlgebra.single 0 r = AddMonoidAlgebra.single 0 r
  rfl

theorem coordinateFirstDirectAwayMap_laurent_C_right
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (r : R) :
    coordinateFirstTargetLaurentRingHom (R := R) a
        ((chartRingEquiv R (a.1 1).down).symm (C r)) =
      AddMonoidAlgebra.single 0 r := by
  change
    AddMonoidAlgebra.mapDomain
      (coordinateLaurentExponentDeleteZeroAddMonoidHom a)
      (AddMonoidAlgebra.mapDomain
        (laurentExponentAwayMap
          (coordinateTailExponent
            (fun l => ((a.delete 0).1 l).down))).toAddMonoidHom
        (chartRingEquiv R (a.1 1).down
          ((chartRingEquiv R (a.1 1).down).symm (C r)))) = _
  rw [RingEquiv.apply_symm_apply]
  change AddMonoidAlgebra.mapDomain
      (coordinateLaurentExponentDeleteZeroAddMonoidHom a)
      (AddMonoidAlgebra.mapDomain
        (laurentExponentAwayMap
          (coordinateTailExponent
            (fun l => ((a.delete 0).1 l).down))).toAddMonoidHom
        (AddMonoidAlgebra.single 0 r)) = _
  rw [AddMonoidAlgebra.mapDomain_single,
    AddMonoidAlgebra.mapDomain_single, map_zero, map_zero]

theorem coordinateFirstDirectAwayMap_laurent_C
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (r : R) :
    coordinateFirstDirectLaurentRingHom (R := R) a
        ((chartRingEquiv R (a.1 1).down).symm (C r)) =
      coordinateFirstTargetLaurentRingHom (R := R) a
        ((chartRingEquiv R (a.1 1).down).symm (C r)) :=
  (coordinateFirstDirectAwayMap_laurent_C_left (R := R) a r).trans
    (coordinateFirstDirectAwayMap_laurent_C_right (R := R) a r).symm

theorem coordinateFirstDirectAwayMap_laurent_X_left
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : {j : σ // j ≠ (a.1 1).down}) :
    coordinateFirstDirectLaurentRingHom (R := R) a
        ((chartRingEquiv R (a.1 1).down).symm (X j)) =
      AddMonoidAlgebra.single
      (coordinateLaurentExponentDeleteZeroAddMonoidHom a
        (laurentExponentAwayMap
          (coordinateTailExponent
            (fun l => ((a.delete 0).1 l).down))
          (Finsupp.single j 1))) 1 := by
  change laurentMonomialRingEquiv R
      (coordinateTailExponent (fun l => (a.1 l).down))
      (coordinateProductAwayRingEquiv (R := R) (fun l => (a.1 l).down)
        (coordinateFirstDirectAwayMap (R := R) a
          ((chartRingEquiv R (a.1 1).down).symm (X j)))) = _
  rw [chartRingEquiv_symm_X,
    coordinateFirstDirectAwayMap_awayVar_laurent]

theorem coordinateFirstDirectAwayMap_laurent_X_right
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : {j : σ // j ≠ (a.1 1).down}) :
    coordinateFirstTargetLaurentRingHom (R := R) a
        ((chartRingEquiv R (a.1 1).down).symm (X j)) =
      AddMonoidAlgebra.single
        (coordinateLaurentExponentDeleteZeroAddMonoidHom a
          (laurentExponentAwayMap
            (coordinateTailExponent
              (fun l => ((a.delete 0).1 l).down))
            (Finsupp.single j 1))) 1 := by
  change
    AddMonoidAlgebra.mapDomain
      (coordinateLaurentExponentDeleteZeroAddMonoidHom a)
      (AddMonoidAlgebra.mapDomain
        (laurentExponentAwayMap
          (coordinateTailExponent
            (fun l => ((a.delete 0).1 l).down))).toAddMonoidHom
        (chartRingEquiv R (a.1 1).down
          ((chartRingEquiv R (a.1 1).down).symm (X j)))) = _
  rw [RingEquiv.apply_symm_apply]
  change AddMonoidAlgebra.mapDomain
      (coordinateLaurentExponentDeleteZeroAddMonoidHom a)
      (AddMonoidAlgebra.mapDomain
        (laurentExponentAwayMap
          (coordinateTailExponent
            (fun l => ((a.delete 0).1 l).down))).toAddMonoidHom
        (AddMonoidAlgebra.single (Finsupp.single j 1) 1)) = _
  rw [AddMonoidAlgebra.mapDomain_single,
    AddMonoidAlgebra.mapDomain_single]
  rfl

theorem coordinateFirstDirectAwayMap_laurent_X
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : {j : σ // j ≠ (a.1 1).down}) :
    coordinateFirstDirectLaurentRingHom (R := R) a
        ((chartRingEquiv R (a.1 1).down).symm (X j)) =
      coordinateFirstTargetLaurentRingHom (R := R) a
        ((chartRingEquiv R (a.1 1).down).symm (X j)) :=
  (coordinateFirstDirectAwayMap_laurent_X_left (R := R) a j).trans
    (coordinateFirstDirectAwayMap_laurent_X_right (R := R) a j).symm

theorem coordinateFirstDirectAwayMap_laurent_chart
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    (coordinateFirstDirectLaurentRingHom (R := R) a).comp
        (chartRingEquiv R (a.1 1).down).symm.toRingHom =
      (coordinateFirstTargetLaurentRingHom (R := R) a).comp
        (chartRingEquiv R (a.1 1).down).symm.toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    exact coordinateFirstDirectAwayMap_laurent_C (R := R) a r
  · intro j
    exact coordinateFirstDirectAwayMap_laurent_X (R := R) a j

theorem coordinateFirstDirectAwayMap_laurent_apply
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (q : HomogeneousLocalization.Away
      (homogeneousSubmodule σ R) (X (a.1 1).down)) :
    coordinateFirstDirectLaurentRingHom (R := R) a q =
      coordinateFirstTargetLaurentRingHom (R := R) a q := by
  have hq := RingHom.congr_fun
    (coordinateFirstDirectAwayMap_laurent_chart (R := R) a)
    (chartRingEquiv R (a.1 1).down q)
  change coordinateFirstDirectLaurentRingHom (R := R) a
      ((chartRingEquiv R (a.1 1).down).symm
        (chartRingEquiv R (a.1 1).down q)) =
    coordinateFirstTargetLaurentRingHom (R := R) a
      ((chartRingEquiv R (a.1 1).down).symm
        (chartRingEquiv R (a.1 1).down q)) at hq
  rw [RingEquiv.symm_apply_apply] at hq
  exact hq


end
end MvPolynomial
