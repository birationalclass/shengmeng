/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
module

public import Linear.ProjectiveLaurentInitialChartMap

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

theorem coordinateProductAwayMap_comp_delete_zero
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    (HomogeneousLocalization.awayMap
      (homogeneousSubmodule σ R)
      (X_mem_homogeneousSubmodule_one R (a.1 0).down)
      (coordinateProductPolynomial_eq_delete_mul (R := R) a 0)).comp
        (HomogeneousLocalization.awayMap
          (homogeneousSubmodule σ R)
          (coordinateTailPolynomial_mem (R := R)
            (fun l => ((a.delete 0).1 l).down)) rfl) =
      coordinateFirstDirectAwayMap (R := R) a := by
  exact HomogeneousLocalization.awayMap_comp
    (homogeneousSubmodule σ R)
    (X_mem_homogeneousSubmodule_one R (a.1 1).down)
    (coordinateTailPolynomial_mem (R := R)
      (fun l => ((a.delete 0).1 l).down))
    (X_mem_homogeneousSubmodule_one R (a.1 0).down)
    rfl
    (coordinateProductPolynomial_eq_delete_mul (R := R) a 0)
    (coordinateProductPolynomial_first_anchor_factor (R := R) a)

/-- Laurent coordinates identify first-entry restriction with the exponent map that changes from
the second-coordinate chart to the first-coordinate chart. -/
theorem coordinateProductAwayLaurentRingEquiv_naturality_delete_zero
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    (laurentMonomialRingEquiv R
        (coordinateTailExponent (fun l => (a.1 l).down))).toRingHom.comp
        ((coordinateProductAwayRingEquiv (R := R)
          (fun l => (a.1 l).down)).toRingHom.comp
          (HomogeneousLocalization.awayMap
            (homogeneousSubmodule σ R)
            (X_mem_homogeneousSubmodule_one R (a.1 0).down)
            (coordinateProductPolynomial_eq_delete_mul (R := R) a 0))) =
      (AddMonoidAlgebra.mapDomainRingHom R
        (coordinateLaurentExponentDeleteZeroAddMonoidHom a)).comp
        ((laurentMonomialRingEquiv R
          (coordinateTailExponent
            (fun l => ((a.delete 0).1 l).down))).toRingHom.comp
          (coordinateProductAwayRingEquiv (R := R)
            (fun l => ((a.delete 0).1 l).down)).toRingHom) := by
  letI := (HomogeneousLocalization.awayMap
    (f := X (a.1 1).down)
    (g := coordinateTailPolynomial (R := R)
      (fun l => ((a.delete 0).1 l).down))
    (x := coordinateProductPolynomial (R := R)
      (fun l => ((a.delete 0).1 l).down))
    (homogeneousSubmodule σ R)
    (coordinateTailPolynomial_mem (R := R)
      (fun l => ((a.delete 0).1 l).down)) rfl).toAlgebra
  let t : HomogeneousLocalization.Away (homogeneousSubmodule σ R)
      (X (a.1 1).down) :=
    HomogeneousLocalization.Away.isLocalizationElem
      (X_mem_homogeneousSubmodule_one R (a.1 1).down)
      (coordinateTailPolynomial_mem (R := R)
        (fun l => ((a.delete 0).1 l).down))
  letI : IsLocalization.Away t
      (HomogeneousLocalization.Away (homogeneousSubmodule σ R)
        (coordinateProductPolynomial (R := R)
          (fun l => ((a.delete 0).1 l).down))) :=
    HomogeneousLocalization.Away.isLocalization_mul
      (X_mem_homogeneousSubmodule_one R (a.1 1).down)
      (coordinateTailPolynomial_mem (R := R)
        (fun l => ((a.delete 0).1 l).down)) rfl one_ne_zero
  apply IsLocalization.ringHom_ext (Submonoid.powers t)
  apply DFunLike.ext _ _
  intro q
  simp only [RingHom.comp_apply]
  rw [show algebraMap
      (HomogeneousLocalization.Away (homogeneousSubmodule σ R) (X (a.1 1).down))
      (HomogeneousLocalization.Away (homogeneousSubmodule σ R)
        (coordinateProductPolynomial (R := R)
          (fun l => ((a.delete 0).1 l).down))) q =
    HomogeneousLocalization.awayMap
      (f := X (a.1 1).down)
      (g := coordinateTailPolynomial (R := R)
        (fun l => ((a.delete 0).1 l).down))
      (x := coordinateProductPolynomial (R := R)
        (fun l => ((a.delete 0).1 l).down))
      (homogeneousSubmodule σ R)
      (coordinateTailPolynomial_mem (R := R)
        (fun l => ((a.delete 0).1 l).down)) rfl q from rfl]
  calc
    _ = coordinateFirstDirectLaurentRingHom (R := R) a q := by
      exact congrArg
        (fun y => laurentMonomialRingEquiv R
          (coordinateTailExponent (fun l => (a.1 l).down))
          (coordinateProductAwayRingEquiv (R := R) (fun l => (a.1 l).down) y))
        (DFunLike.congr_fun
          (coordinateProductAwayMap_comp_delete_zero (R := R) a) q)
    _ = coordinateFirstTargetLaurentRingHom (R := R) a q :=
      coordinateFirstDirectAwayMap_laurent_apply (R := R) a q
    _ = _ := congrArg
      (AddMonoidAlgebra.mapDomain
        (coordinateLaurentExponentDeleteZeroAddMonoidHom a))
      (coordinateProductAwayLaurentRingEquiv_awayMap
        (R := R) (n := n)
        (fun l => ((a.delete 0).1 l).down) q).symm

/-- On sections of standard Cech intersections, deleting the first entry becomes the corresponding
first-anchor Laurent exponent map. -/
theorem coordinateOpenCechIntersectionLaurentRingEquiv_naturality_delete_zero
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (x : Γ(Proj (homogeneousSubmodule σ R),
      coordinateOpenCechIntersection (R := R) (a.delete 0).1)) :
    coordinateOpenCechIntersectionLaurentRingEquiv (R := R) a.1
        ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (coordinateOpenCechDelete (R := R) a 0).op x) =
      AddMonoidAlgebra.mapDomain
        (coordinateLaurentExponentDeleteZeroAddMonoidHom a)
        (coordinateOpenCechIntersectionLaurentRingEquiv
          (R := R) (a.delete 0).1 x) := by
  let q := (coordinateOpenCechIntersectionAwayIso
    (R := R) (a.delete 0).1).inv.hom x
  have hNat := coordinateOpenCechIntersectionAwayIso_naturality_delete
    (R := R) a 0
  have hNatq := ConcreteCategory.congr_hom hNat q
  change (coordinateOpenCechIntersectionAwayIso (R := R) a.1).hom.hom
      (HomogeneousLocalization.awayMap
        (homogeneousSubmodule σ R)
        (X_mem_homogeneousSubmodule_one R (a.1 0).down)
        (coordinateProductPolynomial_eq_delete_mul (R := R) a 0) q) =
    ((Proj (homogeneousSubmodule σ R)).presheaf.map
      (coordinateOpenCechDelete (R := R) a 0).op).hom
      ((coordinateOpenCechIntersectionAwayIso
        (R := R) (a.delete 0).1).hom.hom q) at hNatq
  have hq : (coordinateOpenCechIntersectionAwayIso (R := R) a.1).inv.hom
      (((Proj (homogeneousSubmodule σ R)).presheaf.map
        (coordinateOpenCechDelete (R := R) a 0).op).hom x) =
    HomogeneousLocalization.awayMap
      (homogeneousSubmodule σ R)
      (X_mem_homogeneousSubmodule_one R (a.1 0).down)
      (coordinateProductPolynomial_eq_delete_mul (R := R) a 0) q := by
    apply (coordinateOpenCechIntersectionAwayIso
      (R := R) a.1).commRingCatIsoToRingEquiv.injective
    change (coordinateOpenCechIntersectionAwayIso (R := R) a.1).hom.hom
        ((coordinateOpenCechIntersectionAwayIso (R := R) a.1).inv.hom
          (((Proj (homogeneousSubmodule σ R)).presheaf.map
            (coordinateOpenCechDelete (R := R) a 0).op).hom x)) =
      (coordinateOpenCechIntersectionAwayIso (R := R) a.1).hom.hom
        (HomogeneousLocalization.awayMap
          (homogeneousSubmodule σ R)
          (X_mem_homogeneousSubmodule_one R (a.1 0).down)
          (coordinateProductPolynomial_eq_delete_mul (R := R) a 0) q)
    rw [Iso.inv_hom_id_apply]
    rw [show (coordinateOpenCechIntersectionAwayIso
      (R := R) (a.delete 0).1).hom.hom q = x by
        simpa only [q] using
          (Iso.inv_hom_id_apply
            (coordinateOpenCechIntersectionAwayIso
              (R := R) (a.delete 0).1) x)] at hNatq
    exact hNatq.symm
  change laurentMonomialRingEquiv R
      (coordinateTailExponent (fun l => (a.1 l).down))
      (coordinateProductAwayRingEquiv (R := R) (fun l => (a.1 l).down)
        ((coordinateOpenCechIntersectionAwayIso (R := R) a.1).inv.hom
          (((Proj (homogeneousSubmodule σ R)).presheaf.map
            (coordinateOpenCechDelete (R := R) a 0).op).hom x))) = _
  rw [hq]
  exact DFunLike.congr_fun
    (coordinateProductAwayLaurentRingEquiv_naturality_delete_zero
      (R := R) a) q

/-- Restriction along the first Cech face is the first-anchor exponent map after extending
Laurent coefficients to global sections of the affine base. -/
theorem coordinateOpenCechIntersectionBaseLaurentLinearEquiv_naturality_delete_zero
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (x : Scheme.Modules.baseCechFactor
      (homogeneousProjπ (R := R) (σ := σ))
      (SheafOfModules.unit (Proj (homogeneousSubmodule σ R)).ringCatSheaf)
      (coordinateOpenCover (R := R) (σ := σ)) n (a.delete 0).1) :
    coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := R) a.1
        ((Scheme.Modules.baseModulePresheaf
          (homogeneousProjπ (R := R) (σ := σ))
          (SheafOfModules.unit (Proj (homogeneousSubmodule σ R)).ringCatSheaf)).map
            (coordinateOpenCechDelete (R := R) a 0).op x) =
      AddMonoidAlgebra.mapDomain
        (coordinateLaurentExponentDeleteZeroAddMonoidHom a)
        (coordinateOpenCechIntersectionBaseLaurentLinearEquiv
          (R := R) (a.delete 0).1 x) := by
  let e := (Scheme.ΓSpecIso
    (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm
  let y := coordinateOpenCechIntersectionLaurentRingEquiv
    (R := R) (a.delete 0).1 x
  change AddMonoidAlgebra.mapRingEquiv _ e
      (coordinateOpenCechIntersectionLaurentRingEquiv (R := R) a.1
        ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (coordinateOpenCechDelete (R := R) a 0).op x)) =
    AddMonoidAlgebra.mapDomain
      (coordinateLaurentExponentDeleteZeroAddMonoidHom a)
      (AddMonoidAlgebra.mapRingEquiv _ e y)
  rw [coordinateOpenCechIntersectionLaurentRingEquiv_naturality_delete_zero
    (R := R) a x]
  exact DFunLike.congr_fun
    (AddMonoidAlgebra.mapRingHom_comp_mapDomainRingHom e.toRingHom
      (coordinateLaurentExponentDeleteZeroAddMonoidHom a)) y


end
end MvPolynomial
