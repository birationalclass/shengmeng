/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
The finite weight-assembly and support-contraction pattern reuses the
reviewed AINTLIB adaptation in Linear.ProjectiveLaurentPositiveBoundary.
This file proves the new canonical negative-degree kernel calculation.
-/
module
public import Linear.ProjectiveCanonicalResidue
public import Linear.ProjectiveLaurentCardinality
public import Linear.ProjectiveLaurentWeightAssembly
public import Linear.OrderedCechSupportAlternating
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} {σ : Type} [CommRing R] [Fintype σ] [LinearOrder σ]

/-- A zero top residue forces the entire canonical-weight component to zero,
since there is exactly one ordered tuple in the top degree. -/
theorem coordinateCanonicalResidue_component_eq_zero (n : ℕ)
    (hc : Fintype.card σ = n+1)
    (s : coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) (-(Fintype.card σ : ℤ)) n)
    (hs : coordinateCanonicalResidue (R := R) n hc s = 0) :
    coordinateHomogeneousLaurentWeightComponent (R := R)
      (-(Fintype.card σ : ℤ)) (HomogeneousLaurentExponent.canonicalNegative σ) n s = 0 := by
  apply (LinearStudy.orderedCechSupport_top_eval_eq_zero_iff
    (coordinateCanonicalBaseRing R) _ n (by simpa using hc) _).mp
  exact hs

/-- A top cocycle of canonical negative degree and zero residue is an ACTUAL
Cech boundary. Noncanonical weights contract and the canonical component is
zero; the finite assembly theorem provides one actual preimage. -/
theorem exists_preimage_coordinateCanonicalResidue_zero (n : ℕ)
    (hc : Fintype.card σ = n+2)
    (s : coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) (-(Fintype.card σ : ℤ)) (n+1))
    (hs : coordinateCanonicalResidue (R := R) (n+1) hc s = 0) :
    ∃ t : coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) (-(Fintype.card σ : ℤ)) n,
      (coordinateHomogeneousLaurentOrderedCechDifferential (R := R)
        (σ := σ) (-(Fintype.card σ : ℤ)) n).hom t = s := by
  classical
  let d : ℤ := -(Fintype.card σ : ℤ)
  have hcycle := coordinateHomogeneousLaurent_top_is_cycle d (n+1) hc s
  have hcomponent_cycle (e : HomogeneousLaurentExponent σ d) :
      LinearStudy.orderedCechSupportDifferential (coordinateCanonicalBaseRing R)
        e.liftedNegativeSupport (n+1)
        (coordinateHomogeneousLaurentWeightComponent (R := R) d e (n+1) s) = 0 := by
    rw [← coordinateHomogeneousLaurentWeightComponent_differential,hcycle]
    exact map_zero _
  have hpreimage (e : HomogeneousLaurentExponent σ d) :
      ∃ t : LinearStudy.OrderedCechSupportCochain (coordinateCanonicalBaseRing R)
        e.liftedNegativeSupport n,
      LinearStudy.orderedCechSupportDifferential (coordinateCanonicalBaseRing R)
        e.liftedNegativeSupport n t =
        coordinateHomogeneousLaurentWeightComponent (R := R) d e (n+1) s := by
    by_cases he : e = HomogeneousLaurentExponent.canonicalNegative σ
    · subst e
      refine ⟨0,?_⟩
      rw [coordinateCanonicalResidue_component_eq_zero (n+1) hc s hs,map_zero]
    · obtain ⟨i,hi⟩ := e.exists_outside_support_of_ne_canonical he
      exact LinearStudy.exists_preimage_orderedCechSupportDifferential
        (coordinateCanonicalBaseRing R) e.liftedNegativeSupport i hi n
        (coordinateHomogeneousLaurentWeightComponent (R := R) d e (n+1) s)
        (hcomponent_cycle e)
  choose t ht using hpreimage
  refine ⟨∑ e ∈ coordinateHomogeneousLaurentActiveWeights d (n+1) s,
    coordinateHomogeneousLaurentWeightInclusion (R := R) d e n (t e),?_⟩
  rw [map_sum]
  calc
    (∑ e ∈ coordinateHomogeneousLaurentActiveWeights d (n+1) s,
      (coordinateHomogeneousLaurentOrderedCechDifferential (R := R) d n).hom
        (coordinateHomogeneousLaurentWeightInclusion (R := R) d e n (t e))) =
      ∑ e ∈ coordinateHomogeneousLaurentActiveWeights d (n+1) s,
        coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n+1)
          (coordinateHomogeneousLaurentWeightComponent (R := R) d e (n+1) s) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [coordinateHomogeneousLaurentWeightInclusion_differential,ht e]
    _ = s := coordinateHomogeneousLaurentActiveWeights_reconstruct d (n+1) s

end MvPolynomial
