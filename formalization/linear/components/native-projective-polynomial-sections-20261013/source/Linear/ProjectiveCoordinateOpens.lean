/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-A2d (step 4).
-/
module
public import Linear.ProjectiveSpaceChart
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
@[expose] public section
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory HomogeneousIdeal
noncomputable section
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
/-- The structure morphism from the polynomial `Proj` to the coefficient ring. -/
def homogeneousProjπ :
    Proj (homogeneousSubmodule σ R) ⟶ Spec (.of R) :=
  Proj.toSpecZero (homogeneousSubmodule σ R) ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap R (↥(homogeneousSubmodule σ R 0))))

lemma irrelevant_toIdeal_le_span_range_X :
    (irrelevant (homogeneousSubmodule σ R)).toIdeal ≤
      Ideal.span (Set.range (X : σ → MvPolynomial σ R)) := by
  rw [toIdeal_irrelevant_le]
  intro n hn p hp
  change p ∈ Ideal.span (Set.range (X : σ → MvPolynomial σ R))
  rw [← idealOfVars, ← pow_one (idealOfVars σ R), mem_pow_idealOfVars_iff]
  intro m hm
  have hdegree := ((mem_homogeneousSubmodule _ _).mp hp).degree_eq_sum_deg_support hm
  have hn' : 1 ≤ n := hn
  simpa [Finsupp.degree_apply, ← hdegree] using hn'

/-- A standard coordinate open in polynomial projective space. -/
abbrev coordinateOpen (i : σ) :
    (Proj (homogeneousSubmodule σ R)).Opens :=
  Proj.basicOpen (homogeneousSubmodule σ R) (X i)

/-- Every standard coordinate open in polynomial projective space is affine. -/
lemma coordinateOpen_isAffineOpen (i : σ) :
    IsAffineOpen (coordinateOpen (R := R) i) :=
  Proj.isAffineOpen_basicOpen (homogeneousSubmodule σ R) (X i)
    (X_mem_homogeneousSubmodule_one R i) one_pos

/-- The standard coordinate opens cover polynomial projective space. -/
lemma iSup_coordinateOpen_eq_top :
    ⨆ i : σ, coordinateOpen (R := R) i = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  exact irrelevant_toIdeal_le_span_range_X


end
end MvPolynomial
