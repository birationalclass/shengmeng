/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-A2d (step 4).
-/
module
public import Linear.ProjectiveLaurentNoninitialRestriction
@[expose] public section
set_option backward.privateInPublic true
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
section
local instance : DecidableEq σ := Classical.decEq σ
/-- The inclusion of a full ordered Cech intersection into the intersection obtained by deleting
one entry. -/
abbrev coordinateOpenCechDelete [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) :
    coordinateOpenCechIntersection (R := R) a.1 ⟶
      coordinateOpenCechIntersection (R := R) (a.delete k).1 :=
  (((FormalCoproduct.mk _ (coordinateOpenCover (R := R) (σ := σ))).mapPower
    (SimplexCategory.δ k).toOrderHom.toFun).φ a.1)

/-- Restriction from a deleted Cech intersection to the full intersection is the homogeneous
localization map at the removed coordinate. -/
theorem coordinateOpenCechIntersectionAwayIso_naturality_delete [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) :
    CommRingCat.ofHom
        (HomogeneousLocalization.awayMap
          (homogeneousSubmodule σ R)
          (X_mem_homogeneousSubmodule_one R (a.1 k).down)
          (coordinateProductPolynomial_eq_delete_mul (R := R) a k)) ≫
      (coordinateOpenCechIntersectionAwayIso (R := R) a.1).hom =
    (coordinateOpenCechIntersectionAwayIso (R := R) (a.delete k).1).hom ≫
      (Proj (homogeneousSubmodule σ R)).presheaf.map
        (coordinateOpenCechDelete (R := R) a k).op := by
  simp only [coordinateOpenCechIntersectionAwayIso, Iso.trans_hom,
    Functor.mapIso_hom, Proj.basicOpenIsoAway, asIso_hom]
  rw [← Category.assoc, Proj.awayMap_awayToSection]
  simp only [Category.assoc]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- Restriction from the first standard chart to a full Cech intersection is the homogeneous
localization map at the product of the remaining coordinates. -/
theorem coordinateOpenCechIntersectionAwayIso_naturality_firstChart {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    CommRingCat.ofHom
        (HomogeneousLocalization.awayMap
          (f := X (a 0).down)
          (g := coordinateTailPolynomial (R := R) (fun k => (a k).down))
          (x := coordinateProductPolynomial (R := R) (fun k => (a k).down))
          (homogeneousSubmodule σ R)
          (coordinateTailPolynomial_mem (R := R) (fun k => (a k).down))
          (show coordinateProductPolynomial (R := R) (fun k => (a k).down) =
            X (a 0).down * coordinateTailPolynomial (R := R) (fun k => (a k).down)
            by rw [coordinateProductPolynomial])) ≫
      (coordinateOpenCechIntersectionAwayIso (R := R) a).hom =
    (Proj.basicOpenIsoAway (homogeneousSubmodule σ R) (X (a 0).down)
        (X_mem_homogeneousSubmodule_one R (a 0).down) one_pos).hom ≫
      (Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (coordinateOpenCechIntersection_le (R := R) a 0)).op := by
  simp only [coordinateOpenCechIntersectionAwayIso, Iso.trans_hom,
    Functor.mapIso_hom, Proj.basicOpenIsoAway, asIso_hom]
  rw [← Category.assoc, Proj.awayMap_awayToSection]
  simp only [Category.assoc]
  rw [← Functor.map_comp]
  congr 1

/-- Laurent coordinates carry noninitial restriction between standard Cech intersections to the
inclusion that preserves the underlying local exponent. -/
theorem coordinateOpenCechIntersectionLaurentRingEquiv_naturality_delete_succ
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1))
    (x : Γ(Proj (homogeneousSubmodule σ R),
      coordinateOpenCechIntersection (R := R) (a.delete k.succ).1)) :
    coordinateOpenCechIntersectionLaurentRingEquiv (R := R) a.1
        ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (coordinateOpenCechDelete (R := R) a k.succ).op x) =
      AddMonoidAlgebra.mapDomain
        (coordinateLaurentExponentDeleteAddMonoidHom a k)
        (coordinateOpenCechIntersectionLaurentRingEquiv
          (R := R) (a.delete k.succ).1 x) := by
  let q := (coordinateOpenCechIntersectionAwayIso
    (R := R) (a.delete k.succ).1).inv.hom x
  have hNat := coordinateOpenCechIntersectionAwayIso_naturality_delete
    (R := R) a k.succ
  have hNatq := ConcreteCategory.congr_hom hNat q
  change (coordinateOpenCechIntersectionAwayIso (R := R) a.1).hom.hom
      (HomogeneousLocalization.awayMap
        (homogeneousSubmodule σ R)
        (X_mem_homogeneousSubmodule_one R (a.1 k.succ).down)
        (coordinateProductPolynomial_eq_delete_mul (R := R) a k.succ) q) =
    ((Proj (homogeneousSubmodule σ R)).presheaf.map
      (coordinateOpenCechDelete (R := R) a k.succ).op).hom
      ((coordinateOpenCechIntersectionAwayIso
        (R := R) (a.delete k.succ).1).hom.hom q) at hNatq
  have hq : (coordinateOpenCechIntersectionAwayIso (R := R) a.1).inv.hom
      (((Proj (homogeneousSubmodule σ R)).presheaf.map
        (coordinateOpenCechDelete (R := R) a k.succ).op).hom x) =
    HomogeneousLocalization.awayMap
      (homogeneousSubmodule σ R)
      (X_mem_homogeneousSubmodule_one R (a.1 k.succ).down)
      (coordinateProductPolynomial_eq_delete_mul (R := R) a k.succ) q := by
    apply (coordinateOpenCechIntersectionAwayIso
      (R := R) a.1).commRingCatIsoToRingEquiv.injective
    change (coordinateOpenCechIntersectionAwayIso (R := R) a.1).hom.hom
        ((coordinateOpenCechIntersectionAwayIso (R := R) a.1).inv.hom
          (((Proj (homogeneousSubmodule σ R)).presheaf.map
            (coordinateOpenCechDelete (R := R) a k.succ).op).hom x)) =
      (coordinateOpenCechIntersectionAwayIso (R := R) a.1).hom.hom
        (HomogeneousLocalization.awayMap
          (homogeneousSubmodule σ R)
          (X_mem_homogeneousSubmodule_one R (a.1 k.succ).down)
          (coordinateProductPolynomial_eq_delete_mul (R := R) a k.succ) q)
    rw [Iso.inv_hom_id_apply]
    rw [show (coordinateOpenCechIntersectionAwayIso
      (R := R) (a.delete k.succ).1).hom.hom q = x by
        simpa only [q] using
          (Iso.inv_hom_id_apply
            (coordinateOpenCechIntersectionAwayIso
              (R := R) (a.delete k.succ).1) x)] at hNatq
    exact hNatq.symm
  change laurentMonomialRingEquiv R
      (coordinateTailExponent (fun l => (a.1 l).down))
      (coordinateProductAwayRingEquiv (R := R) (fun l => (a.1 l).down)
        ((coordinateOpenCechIntersectionAwayIso (R := R) a.1).inv.hom
          (((Proj (homogeneousSubmodule σ R)).presheaf.map
            (coordinateOpenCechDelete (R := R) a k.succ).op).hom x))) = _
  rw [hq]
  exact DFunLike.congr_fun
    (coordinateProductAwayLaurentRingEquiv_naturality_delete_succ
      (R := R) a k) q

/-- After transporting coefficients to the affine base, noninitial restriction still preserves the
underlying local Laurent exponent. -/
theorem coordinateOpenCechIntersectionBaseLaurentLinearEquiv_naturality_delete_succ
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1))
    (x : Scheme.Modules.baseCechFactor
      (homogeneousProjπ (R := R) (σ := σ))
      (SheafOfModules.unit (Proj (homogeneousSubmodule σ R)).ringCatSheaf)
      (coordinateOpenCover (R := R) (σ := σ)) n (a.delete k.succ).1) :
    coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := R) a.1
        ((Scheme.Modules.baseModulePresheaf
          (homogeneousProjπ (R := R) (σ := σ))
          (SheafOfModules.unit (Proj (homogeneousSubmodule σ R)).ringCatSheaf)).map
            (coordinateOpenCechDelete (R := R) a k.succ).op x) =
      AddMonoidAlgebra.mapDomain
        (coordinateLaurentExponentDeleteAddMonoidHom a k)
        (coordinateOpenCechIntersectionBaseLaurentLinearEquiv
          (R := R) (a.delete k.succ).1 x) := by
  let e := (Scheme.ΓSpecIso
    (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm
  let y := coordinateOpenCechIntersectionLaurentRingEquiv
    (R := R) (a.delete k.succ).1 x
  change AddMonoidAlgebra.mapRingEquiv _ e
      (coordinateOpenCechIntersectionLaurentRingEquiv (R := R) a.1
        ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (coordinateOpenCechDelete (R := R) a k.succ).op x)) =
    AddMonoidAlgebra.mapDomain
      (coordinateLaurentExponentDeleteAddMonoidHom a k)
      (AddMonoidAlgebra.mapRingEquiv _ e y)
  rw [coordinateOpenCechIntersectionLaurentRingEquiv_naturality_delete_succ
    (R := R) a k x]
  exact DFunLike.congr_fun
    (AddMonoidAlgebra.mapRingHom_comp_mapDomainRingHom e.toRingHom
      (coordinateLaurentExponentDeleteAddMonoidHom a k)) y

/-- In global homogeneous-weight coordinates, a noninitial restriction is the existing deleted-
tuple inclusion. -/
theorem
    coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv_naturality_delete_succ
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1)) (d : ℤ)
    (x : Scheme.Modules.baseCechFactor
      (homogeneousProjπ (R := R) (σ := σ))
      (SheafOfModules.unit (Proj (homogeneousSubmodule σ R)).ringCatSheaf)
      (coordinateOpenCover (R := R) (σ := σ)) n (a.delete k.succ).1) :
    coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
        (R := R) a.1 d
        ((Scheme.Modules.baseModulePresheaf
          (homogeneousProjπ (R := R) (σ := σ))
          (SheafOfModules.unit (Proj (homogeneousSubmodule σ R)).ringCatSheaf)).map
            (coordinateOpenCechDelete (R := R) a k.succ).op x) =
      coordinateHomogeneousLaurentDeleteLinearMap (R := R) a k.succ d
        (coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
          (R := R) (a.delete k.succ).1 d x) := by
  let S := Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
  let y := coordinateOpenCechIntersectionBaseLaurentLinearEquiv
    (R := R) (a.delete k.succ).1 x
  change AddMonoidAlgebra.mapDomainLinearEquiv S S
      (coordinateLaurentExponentEquiv (fun l => (a.1 l).down) d)
      (coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := R) a.1
        ((Scheme.Modules.baseModulePresheaf
          (homogeneousProjπ (R := R) (σ := σ))
          (SheafOfModules.unit (Proj (homogeneousSubmodule σ R)).ringCatSheaf)).map
            (coordinateOpenCechDelete (R := R) a k.succ).op x)) =
    AddMonoidAlgebra.mapDomainLinearMap S S
      (coordinateLaurentExponentDeleteEmbedding a k.succ d)
      (AddMonoidAlgebra.mapDomainLinearEquiv S S
        (coordinateLaurentExponentEquiv
          (fun l => ((a.delete k.succ).1 l).down) d) y)
  rw [coordinateOpenCechIntersectionBaseLaurentLinearEquiv_naturality_delete_succ
    (R := R) a k x]
  change AddMonoidAlgebra.mapDomainLinearEquiv S S
      (coordinateLaurentExponentEquiv (fun l => (a.1 l).down) d)
      (AddMonoidAlgebra.mapDomain
        (coordinateLaurentExponentDeleteAddMonoidHom a k) y) = _
  induction y using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      simp only [AddMonoidAlgebra.mapDomain_add, map_add, hx, hy]
  | single e r =>
      simp only [AddMonoidAlgebra.mapDomain_single,
        AddMonoidAlgebra.mapDomainLinearEquiv_single,
        AddMonoidAlgebra.mapDomainLinearMap_single]
      rw [coordinateLaurentExponentEquiv_delete_succ a k d e]

/-- A noninitial Cech restriction sends each homogeneous Laurent basis vector to the same global
weight in the full tuple. -/
theorem
    coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv_basis_naturality_delete_succ
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1)) (d : ℤ)
    (e : laurentExponentSubmonoid
      (coordinateTailExponent (fun l => ((a.delete k.succ).1 l).down)))
    (r : Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))) :
    coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
        (R := R) a.1 d
        ((Scheme.Modules.baseModulePresheaf
          (homogeneousProjπ (R := R) (σ := σ))
          (SheafOfModules.unit (Proj (homogeneousSubmodule σ R)).ringCatSheaf)).map
            (coordinateOpenCechDelete (R := R) a k.succ).op
          ((coordinateOpenCechIntersectionBaseLaurentLinearEquiv
            (R := R) (a.delete k.succ).1).symm
            (AddMonoidAlgebra.single e r))) =
      AddMonoidAlgebra.single
        (coordinateLaurentExponentDeleteEmbedding a k.succ d
          (coordinateLaurentExponentEquiv
            (fun l => ((a.delete k.succ).1 l).down) d e)) r := by
  rw [coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv_naturality_delete_succ
    (R := R) a k d]
  rw [coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv_basis_apply]
  exact coordinateHomogeneousLaurentDeleteLinearMap_single
    (R := R) a k.succ d _ r

end


end
end MvPolynomial
