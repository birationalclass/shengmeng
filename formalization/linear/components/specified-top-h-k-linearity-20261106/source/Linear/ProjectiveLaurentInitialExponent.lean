/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
module
public import Linear.ProjectiveCechLaurentRestriction
@[expose] public section
set_option backward.privateInPublic true
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
noncomputable section
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
local instance : DecidableEq σ := Classical.decEq σ
/-- The first two entries of an ordered Cech index are distinct. -/
theorem coordinateOpenCechFirstSecond_ne [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    (a.1 1).down ≠ (a.1 0).down := by
  intro h
  have ha : a.1 1 = a.1 0 := ULift.ext h
  exact one_ne_zero (a.2.injective ha)

/-- The local Laurent exponent of an integer power of the first transition unit. -/
noncomputable def coordinateOpenCechFirstTransitionExponent [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    ℤ →+ laurentExponentSubmonoid
      (coordinateTailExponent (fun k => (a.1 k).down)) where
  toFun d := ⟨Finsupp.single
    (⟨(a.1 1).down, coordinateOpenCechFirstSecond_ne a⟩ :
      {j : σ // j ≠ (a.1 0).down}) d, by
    intro i hi
    by_cases hij : i =
        (⟨(a.1 1).down, coordinateOpenCechFirstSecond_ne a⟩ :
          {j : σ // j ≠ (a.1 0).down})
    · subst i
      exact (coordinateTailExponent_ne_zero_iff
        (fun k => (a.1 k).down)
        (⟨(a.1 1).down, coordinateOpenCechFirstSecond_ne a⟩ :
          {j : σ // j ≠ (a.1 0).down})).2 ⟨1, rfl⟩
    · simp [hij] at hi⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' d e := by
    apply Subtype.ext
    simp

private noncomputable def coordinateLaurentExponentDeleteZeroRaw
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (e : laurentExponentSubmonoid
      (coordinateTailExponent (fun k => ((a.delete 0).1 k).down))) :
    laurentExponentSubmonoid
      (coordinateTailExponent (fun k => (a.1 k).down)) :=
  (coordinateLaurentExponentEquiv (fun k => (a.1 k).down) 0).symm
    (coordinateLaurentExponentDeleteEmbedding a 0 0
      (coordinateLaurentExponentEquiv
        (fun k => ((a.delete 0).1 k).down) 0 e))

private lemma coordinateLaurentExponentDeleteZeroRaw_apply
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (e : laurentExponentSubmonoid
      (coordinateTailExponent (fun k => ((a.delete 0).1 k).down)))
    (j : {j : σ // j ≠ (a.1 0).down}) :
    (coordinateLaurentExponentDeleteZeroRaw a e).1 j =
      (coordinateLaurentExponentEquiv
        (fun k => ((a.delete 0).1 k).down) 0 e).1.1 j.1 := by
  rw [coordinateLaurentExponentDeleteZeroRaw,
    coordinateLaurentExponentEquiv_symm_apply]
  rfl

private theorem coordinateLaurentExponentEquiv_zero_apply_zero
    {n : ℕ} (b : Fin (n + 1) → σ) (i : σ) :
    (coordinateLaurentExponentEquiv b 0
      (0 : laurentExponentSubmonoid (coordinateTailExponent b))).1.1 i = 0 := by
  by_cases hi : i = b 0
  · subst i
    rw [coordinateLaurentExponentEquiv_apply_anchor]
    simp
  · rw [coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _ hi]
    rfl

private theorem coordinateLaurentExponentEquiv_zero_apply_add
    {n : ℕ} (b : Fin (n + 1) → σ)
    (e f : laurentExponentSubmonoid (coordinateTailExponent b)) (i : σ) :
    (coordinateLaurentExponentEquiv b 0 (e + f)).1.1 i =
      (coordinateLaurentExponentEquiv b 0 e).1.1 i +
        (coordinateLaurentExponentEquiv b 0 f).1.1 i := by
  by_cases hi : i = b 0
  · subst i
    rw [coordinateLaurentExponentEquiv_apply_anchor,
      coordinateLaurentExponentEquiv_apply_anchor,
      coordinateLaurentExponentEquiv_apply_anchor]
    change 0 - Finsupp.degree (e.1 + f.1) =
      (0 - Finsupp.degree e.1) + (0 - Finsupp.degree f.1)
    rw [map_add]
    omega
  · rw [coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _ hi,
      coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _ hi,
      coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _ hi]
    rfl

/-- Restricting from the chart anchored at the second coordinate to the full intersection, expressed
in Laurent exponents for the chart anchored at the first coordinate. -/
noncomputable def coordinateLaurentExponentDeleteZeroAddMonoidHom
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    laurentExponentSubmonoid
        (coordinateTailExponent (fun k => ((a.delete 0).1 k).down)) →+
      laurentExponentSubmonoid
        (coordinateTailExponent (fun k => (a.1 k).down)) where
  toFun := coordinateLaurentExponentDeleteZeroRaw a
  map_zero' := by
    apply Subtype.ext
    ext j
    rw [coordinateLaurentExponentDeleteZeroRaw_apply]
    exact coordinateLaurentExponentEquiv_zero_apply_zero
      (fun k => ((a.delete 0).1 k).down) j.1
  map_add' e f := by
    apply Subtype.ext
    ext j
    change (coordinateLaurentExponentDeleteZeroRaw a (e + f)).1 j =
      (coordinateLaurentExponentDeleteZeroRaw a e).1 j +
        (coordinateLaurentExponentDeleteZeroRaw a f).1 j
    rw [coordinateLaurentExponentDeleteZeroRaw_apply,
      coordinateLaurentExponentDeleteZeroRaw_apply,
      coordinateLaurentExponentDeleteZeroRaw_apply]
    exact coordinateLaurentExponentEquiv_zero_apply_add
      (fun k => ((a.delete 0).1 k).down) e f j.1

/-- The first-deletion exponent map reads the same degree-zero global homogeneous exponent in the
new anchor chart. -/
@[simp]
theorem coordinateLaurentExponentDeleteZeroAddMonoidHom_apply
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (e : laurentExponentSubmonoid
      (coordinateTailExponent (fun k => ((a.delete 0).1 k).down)))
    (j : {j : σ // j ≠ (a.1 0).down}) :
    (coordinateLaurentExponentDeleteZeroAddMonoidHom a e).1 j =
      (coordinateLaurentExponentEquiv
        (fun k => ((a.delete 0).1 k).down) 0 e).1.1 j.1 :=
  coordinateLaurentExponentDeleteZeroRaw_apply a e j

@[simp]
private theorem coordinateOpenCechFirstTransitionExponent_apply_second
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (d : ℤ) :
    (coordinateOpenCechFirstTransitionExponent (n := n) a d).1
        ⟨(a.1 1).down, coordinateOpenCechFirstSecond_ne (n := n) a⟩ = d := by
  simp [coordinateOpenCechFirstTransitionExponent]

private theorem coordinateOpenCechFirstTransitionExponent_apply_of_ne
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (d : ℤ)
    (j : {j : σ // j ≠ (a.1 0).down}) (hj : j.1 ≠ (a.1 1).down) :
    (coordinateOpenCechFirstTransitionExponent (n := n) a d).1 j = 0 := by
  have hj' :
      (⟨(a.1 1).down, coordinateOpenCechFirstSecond_ne (n := n) a⟩ :
        {j : σ // j ≠ (a.1 0).down}) ≠ j := by
    intro h
    exact hj (congrArg Subtype.val h).symm
  simp [coordinateOpenCechFirstTransitionExponent, hj']

@[simp]
private theorem coordinateOpenCechFirstTransitionExponent_degree
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (d : ℤ) :
    Finsupp.degree (coordinateOpenCechFirstTransitionExponent (n := n) a d).1 = d := by
  simp [coordinateOpenCechFirstTransitionExponent, Finsupp.degree_single]

private theorem coordinateLaurentExponentDeleteZeroAddMonoidHom_degree
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (e : laurentExponentSubmonoid
      (coordinateTailExponent (fun k => ((a.delete 0).1 k).down))) :
    Finsupp.degree (coordinateLaurentExponentDeleteZeroAddMonoidHom a e).1 =
      - (coordinateLaurentExponentEquiv
        (fun k => ((a.delete 0).1 k).down) 0 e).1.1 (a.1 0).down := by
  have h := (coordinateLaurentExponentEquiv
    (fun k => (a.1 k).down) 0).apply_symm_apply
      (coordinateLaurentExponentDeleteEmbedding a 0 0
        (coordinateLaurentExponentEquiv
          (fun k => ((a.delete 0).1 k).down) 0 e))
  have h0 := congrArg
    (fun z => z.1.1 (a.1 0).down) h
  change (coordinateLaurentExponentEquiv
      (fun k => (a.1 k).down) 0
      (coordinateLaurentExponentDeleteZeroAddMonoidHom a e)).1.1 (a.1 0).down =
    (coordinateLaurentExponentEquiv
      (fun k => ((a.delete 0).1 k).down) 0 e).1.1 (a.1 0).down at h0
  rw [coordinateLaurentExponentEquiv_apply_anchor] at h0
  omega

/-- First-deletion restriction followed by the twist transition gives the same global homogeneous
exponent as inclusion from the deleted tuple. -/
theorem coordinateLaurentExponentEquiv_delete_zero_add_transition
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (d : ℤ)
    (e : laurentExponentSubmonoid
      (coordinateTailExponent (fun k => ((a.delete 0).1 k).down))) :
    coordinateLaurentExponentEquiv (fun k => (a.1 k).down) d
        (coordinateLaurentExponentDeleteZeroAddMonoidHom a e +
          coordinateOpenCechFirstTransitionExponent (n := n) a d) =
      coordinateLaurentExponentDeleteEmbedding a 0 d
        (coordinateLaurentExponentEquiv
          (fun k => ((a.delete 0).1 k).down) d e) := by
  apply Subtype.ext
  apply Subtype.ext
  ext i
  change (coordinateLaurentExponentEquiv (fun k => (a.1 k).down) d
      (coordinateLaurentExponentDeleteZeroAddMonoidHom a e +
        coordinateOpenCechFirstTransitionExponent (n := n) a d)).1.1 i =
    (coordinateLaurentExponentEquiv
      (fun k => ((a.delete 0).1 k).down) d e).1.1 i
  by_cases hi0 : i = (a.1 0).down
  · subst i
    rw [coordinateLaurentExponentEquiv_apply_anchor]
    change d - Finsupp.degree
        ((coordinateLaurentExponentDeleteZeroAddMonoidHom a e).1 +
          (coordinateOpenCechFirstTransitionExponent (n := n) a d).1) = _
    rw [map_add,
      coordinateLaurentExponentDeleteZeroAddMonoidHom_degree,
      coordinateOpenCechFirstTransitionExponent_degree]
    have h01 : (a.1 0).down ≠ ((a.delete 0).1 0).down := by
      exact (coordinateOpenCechFirstSecond_ne (n := n) a).symm
    rw [coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _ h01,
      coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _ h01]
    omega
  · rw [coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _ hi0]
    change (coordinateLaurentExponentDeleteZeroAddMonoidHom a e).1 ⟨i, hi0⟩ +
        (coordinateOpenCechFirstTransitionExponent (n := n) a d).1 ⟨i, hi0⟩ = _
    rw [coordinateLaurentExponentDeleteZeroAddMonoidHom_apply]
    by_cases hi1 : i = (a.1 1).down
    · subst i
      rw [coordinateOpenCechFirstTransitionExponent_apply_second]
      change (coordinateLaurentExponentEquiv
          (fun k => ((a.delete 0).1 k).down) 0 e).1.1
            ((a.delete 0).1 0).down + d = _
      have hanchor : ((a.delete 0).1 0).down = (a.1 1).down := rfl
      rw [← hanchor, coordinateLaurentExponentEquiv_apply_anchor,
        coordinateLaurentExponentEquiv_apply_anchor]
      omega
    · rw [coordinateOpenCechFirstTransitionExponent_apply_of_ne
        (a := a) d ⟨i, hi0⟩ hi1, add_zero]
      have hi1' : i ≠ ((a.delete 0).1 0).down := hi1
      rw [coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _ hi1',
        coordinateLaurentExponentEquiv_apply_of_ne _ _ _ _ hi1']


end
end MvPolynomial
