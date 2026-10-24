/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-A2d (step 4).
-/
module
public import Linear.ProjectiveCechLaurentSections
@[expose] public section
set_option backward.privateInPublic true
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
/-- Deleting a Cech coordinate can only shrink the tuple, so every weight allowed on the deleted
tuple is allowed on the full tuple. -/
def coordinateLaurentExponentDeleteEmbedding [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) (d : ℤ) :
    {e : HomogeneousLaurentExponent σ d //
        e.IsAllowedOn (fun l => ((a.delete k).1 l).down)} ↪
      {e : HomogeneousLaurentExponent σ d //
        e.IsAllowedOn (fun l => (a.1 l).down)} where
  toFun e := ⟨e.1, by
    intro i hi
    obtain ⟨l, hl⟩ := e.2 hi
    refine ⟨k.succAbove l, ?_⟩
    change (a.1 (k.succAbove l)).down = i at hl
    exact hl⟩
  inj' e f h := by
    apply Subtype.ext
    exact congrArg
      (fun x : {e : HomogeneousLaurentExponent σ d //
        e.IsAllowedOn (fun l => (a.1 l).down)} => x.1) h

/-- The weight-coordinate form of a Cech coface: include the weights allowed on the deleted tuple
among those allowed on the full tuple. -/
noncomputable def coordinateHomogeneousLaurentDeleteLinearMap [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) (d : ℤ) :
    AddMonoidAlgebra
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        {e : HomogeneousLaurentExponent σ d //
          e.IsAllowedOn (fun l => ((a.delete k).1 l).down)} →ₗ[
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))]
      AddMonoidAlgebra
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        {e : HomogeneousLaurentExponent σ d //
          e.IsAllowedOn (fun l => (a.1 l).down)} :=
  AddMonoidAlgebra.mapDomainLinearMap
    Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
    Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
    (coordinateLaurentExponentDeleteEmbedding a k d)

/-- A Cech deletion map preserves the underlying global homogeneous weight. -/
@[simp]
theorem coordinateHomogeneousLaurentDeleteLinearMap_single [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) (d : ℤ)
    (e : {e : HomogeneousLaurentExponent σ d //
      e.IsAllowedOn (fun l => ((a.delete k).1 l).down)})
    (r : Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))) :
    coordinateHomogeneousLaurentDeleteLinearMap (R := R) a k d
        (AddMonoidAlgebra.single e r) =
      AddMonoidAlgebra.single (coordinateLaurentExponentDeleteEmbedding a k d e) r := by
  exact AddMonoidAlgebra.mapDomainLinearMap_single
    (R := Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens)))
    (S := Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens)))
    (coordinateLaurentExponentDeleteEmbedding a k d) r e

/-- For a noninitial deletion, a local Laurent exponent remains the same exponent and only gains
the enlarged support permission from the full tuple. -/
noncomputable def coordinateLaurentExponentDeleteAddMonoidHom [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1)) :
    laurentExponentSubmonoid
        (coordinateTailExponent (fun l => ((a.delete k.succ).1 l).down)) →+
      laurentExponentSubmonoid
        (coordinateTailExponent (fun l => (a.1 l).down)) where
  toFun e := ⟨e.1, by
    intro i hi
    apply (coordinateTailExponent_ne_zero_iff
      (fun l => (a.1 l).down) i).2
    obtain ⟨l, hl⟩ := (coordinateTailExponent_ne_zero_iff
      (fun l => ((a.delete k.succ).1 l).down) i).1 (e.2 i hi)
    exact ⟨k.succ.succAbove l, hl⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The local exponent inclusion commutes with the natural-exponent maps into the two Laurent
localizations. -/
theorem coordinateLaurentExponentDeleteAddMonoidHom_awayMap [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1))
    (e : {j : σ // j ≠ (a.1 0).down} →₀ ℕ) :
    coordinateLaurentExponentDeleteAddMonoidHom a k
        (laurentExponentAwayMap
          (coordinateTailExponent
            (fun l => ((a.delete k.succ).1 l).down)) e) =
      laurentExponentAwayMap
        (coordinateTailExponent (fun l => (a.1 l).down)) e := by
  apply Subtype.ext
  ext i
  rfl

/-- Reindexing local exponents by homogeneous weights identifies the noninitial local inclusion
with the global deleted-tuple inclusion. -/
theorem coordinateLaurentExponentEquiv_delete_succ [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1)) (d : ℤ)
    (e : laurentExponentSubmonoid
      (coordinateTailExponent (fun l => ((a.delete k.succ).1 l).down))) :
    coordinateLaurentExponentEquiv (fun l => (a.1 l).down) d
        (coordinateLaurentExponentDeleteAddMonoidHom a k e) =
      coordinateLaurentExponentDeleteEmbedding a k.succ d
        (coordinateLaurentExponentEquiv
          (fun l => ((a.delete k.succ).1 l).down) d e) := by
  apply Subtype.ext
  apply Subtype.ext
  ext i
  change (coordinateLaurentExponentEquiv (fun l => (a.1 l).down) d
      (coordinateLaurentExponentDeleteAddMonoidHom a k e)).1.1 i =
    (coordinateLaurentExponentEquiv
      (fun l => ((a.delete k.succ).1 l).down) d e).1.1 i
  have hanchor : ((a.delete k.succ).1 0).down = (a.1 0).down := rfl
  by_cases hi : i = (a.1 0).down
  · subst i
    rw [coordinateLaurentExponentEquiv_apply_anchor]
    change d - Finsupp.degree e.1 =
      (coordinateLaurentExponentEquiv
        (fun l => ((a.delete k.succ).1 l).down) d e).1.1
          ((a.delete k.succ).1 0).down
    exact (coordinateLaurentExponentEquiv_apply_anchor
      (fun l => ((a.delete k.succ).1 l).down) d e).symm
  · have hi' : i ≠ ((a.delete k.succ).1 0).down := by
      simpa [hanchor] using hi
    rw [coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _ hi,
      coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _ hi']
    rfl

section

local instance : DecidableEq σ := Classical.decEq σ

private theorem coordinateLaurentExponentDeleteRingHom_comp [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1)) :
    (AddMonoidAlgebra.mapDomainRingHom R
      (coordinateLaurentExponentDeleteAddMonoidHom a k)).comp
        (AddMonoidAlgebra.mapDomainRingHom R
          (laurentExponentAwayMap
            (coordinateTailExponent
              (fun l => ((a.delete k.succ).1 l).down))).toAddMonoidHom) =
      AddMonoidAlgebra.mapDomainRingHom R
        (laurentExponentAwayMap
          (coordinateTailExponent (fun l => (a.1 l).down))).toAddMonoidHom := by
  rw [← AddMonoidAlgebra.mapDomainRingHom_comp]
  congr 1

/-- For a noninitial deletion, Laurent coordinates identify restriction to the full ordered Cech
intersection with the inclusion that preserves the underlying Laurent exponent. -/
theorem coordinateProductAwayLaurentRingEquiv_naturality_delete_succ
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1)) :
    (laurentMonomialRingEquiv R
        (coordinateTailExponent (fun l => (a.1 l).down))).toRingHom.comp
        ((coordinateProductAwayRingEquiv (R := R)
          (fun l => (a.1 l).down)).toRingHom.comp
          (HomogeneousLocalization.awayMap
            (homogeneousSubmodule σ R)
            (X_mem_homogeneousSubmodule_one R (a.1 k.succ).down)
            (coordinateProductPolynomial_eq_delete_mul (R := R) a k.succ))) =
      (AddMonoidAlgebra.mapDomainRingHom R
        (coordinateLaurentExponentDeleteAddMonoidHom a k)).comp
        ((laurentMonomialRingEquiv R
          (coordinateTailExponent
            (fun l => ((a.delete k.succ).1 l).down))).toRingHom.comp
          (coordinateProductAwayRingEquiv (R := R)
            (fun l => ((a.delete k.succ).1 l).down)).toRingHom) := by
  letI := (HomogeneousLocalization.awayMap
    (f := X (a.1 0).down)
    (g := coordinateTailPolynomial (R := R)
      (fun l => ((a.delete k.succ).1 l).down))
    (x := coordinateProductPolynomial (R := R)
      (fun l => ((a.delete k.succ).1 l).down))
    (homogeneousSubmodule σ R)
    (coordinateTailPolynomial_mem (R := R)
      (fun l => ((a.delete k.succ).1 l).down)) rfl).toAlgebra
  let t : HomogeneousLocalization.Away (homogeneousSubmodule σ R)
      (X (a.1 0).down) :=
    HomogeneousLocalization.Away.isLocalizationElem
      (X_mem_homogeneousSubmodule_one R (a.1 0).down)
      (coordinateTailPolynomial_mem (R := R)
        (fun l => ((a.delete k.succ).1 l).down))
  letI : IsLocalization.Away t
      (HomogeneousLocalization.Away (homogeneousSubmodule σ R)
        (coordinateProductPolynomial (R := R)
          (fun l => ((a.delete k.succ).1 l).down))) :=
    HomogeneousLocalization.Away.isLocalization_mul
      (X_mem_homogeneousSubmodule_one R (a.1 0).down)
      (coordinateTailPolynomial_mem (R := R)
        (fun l => ((a.delete k.succ).1 l).down)) rfl one_ne_zero
  apply IsLocalization.ringHom_ext (Submonoid.powers t)
  apply DFunLike.ext _ _
  intro q
  simp only [RingHom.comp_apply]
  rw [show algebraMap
      (HomogeneousLocalization.Away (homogeneousSubmodule σ R) (X (a.1 0).down))
      (HomogeneousLocalization.Away (homogeneousSubmodule σ R)
        (coordinateProductPolynomial (R := R)
          (fun l => ((a.delete k.succ).1 l).down))) q =
    HomogeneousLocalization.awayMap
      (f := X (a.1 0).down)
      (g := coordinateTailPolynomial (R := R)
        (fun l => ((a.delete k.succ).1 l).down))
      (x := coordinateProductPolynomial (R := R)
        (fun l => ((a.delete k.succ).1 l).down))
      (homogeneousSubmodule σ R)
      (coordinateTailPolynomial_mem (R := R)
        (fun l => ((a.delete k.succ).1 l).down)) rfl q from rfl]
  let p := chartRingEquiv R (a.1 0).down q
  calc
    _ = laurentMonomialRingEquiv R
        (coordinateTailExponent (fun l => (a.1 l).down))
        (coordinateProductAwayRingEquiv (R := R) (fun l => (a.1 l).down)
          (HomogeneousLocalization.awayMap
            (f := X (a.1 0).down)
            (g := coordinateTailPolynomial (R := R) (fun l => (a.1 l).down))
            (x := coordinateProductPolynomial (R := R) (fun l => (a.1 l).down))
            (homogeneousSubmodule σ R)
            (coordinateTailPolynomial_mem (R := R)
              (fun l => (a.1 l).down)) rfl q)) := congrArg
              (fun x => laurentMonomialRingEquiv R
                (coordinateTailExponent (fun l => (a.1 l).down))
                (coordinateProductAwayRingEquiv (R := R)
                  (fun l => (a.1 l).down) x))
              (coordinateTailAwayMap_comp_delete_succ (R := R) a k q)
    _ = AddMonoidAlgebra.mapDomain
        (laurentExponentAwayMap
          (coordinateTailExponent (fun l => (a.1 l).down))).toAddMonoidHom p :=
      coordinateProductAwayLaurentRingEquiv_awayMap
        (R := R) (σ := σ) (n := n + 1) (fun l => (a.1 l).down) q
    _ = AddMonoidAlgebra.mapDomain
        (coordinateLaurentExponentDeleteAddMonoidHom a k)
        (AddMonoidAlgebra.mapDomain
          (laurentExponentAwayMap
            (coordinateTailExponent
              (fun l => ((a.delete k.succ).1 l).down))).toAddMonoidHom p) := by
      change (AddMonoidAlgebra.mapDomainRingHom R
          (laurentExponentAwayMap
            (coordinateTailExponent (fun l => (a.1 l).down))).toAddMonoidHom) p =
        ((AddMonoidAlgebra.mapDomainRingHom R
          (coordinateLaurentExponentDeleteAddMonoidHom a k)).comp
          (AddMonoidAlgebra.mapDomainRingHom R
            (laurentExponentAwayMap
              (coordinateTailExponent
                (fun l => ((a.delete k.succ).1 l).down))).toAddMonoidHom)) p
      exact congrArg (fun f => f p)
        (coordinateLaurentExponentDeleteRingHom_comp (R := R) a k).symm
    _ = _ := congrArg
      (AddMonoidAlgebra.mapDomain
        (coordinateLaurentExponentDeleteAddMonoidHom a k))
      (coordinateProductAwayLaurentRingEquiv_awayMap
        (R := R) (σ := σ) (n := n)
        (fun l => ((a.delete k.succ).1 l).down) q).symm


end
end
end MvPolynomial
