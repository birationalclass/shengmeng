/-
Released under Apache 2.0. The finite weight assembly pattern retains
AINTLIB attribution from Linear.ProjectiveLaurentPositiveBoundary.
-/
module
public import Linear.ProjectiveCanonicalResidueKernel
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} {σ : Type} [CommRing R] [Fintype σ] [LinearOrder σ]

/-- In EVERY integer twist, a top cochain whose full-negative-support
components vanish is an actual boundary. No cycle input is needed in top
degree. This removes the canonical-degree restriction for later pairings. -/
theorem exists_preimage_coordinateLaurent_top_of_full_support_zero (d : ℤ) (n : ℕ)
    (hc : Fintype.card σ = n+2)
    (s : coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d (n+1))
    (hs : ∀ e : HomogeneousLaurentExponent σ d,
      (e.liftedNegativeSupport : Set (ULift.{u} σ)) = Set.univ →
        coordinateHomogeneousLaurentWeightComponent (R := R) d e (n+1) s = 0) :
    ∃ t : coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n,
      (coordinateHomogeneousLaurentOrderedCechDifferential (R := R) (σ := σ) d n).hom t = s := by
  classical
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
    by_cases he : (e.liftedNegativeSupport : Set (ULift.{u} σ)) = Set.univ
    · refine ⟨0,?_⟩
      rw [hs e he,map_zero]
    · have hex : ∃ i : ULift.{u} σ, i ∉ e.liftedNegativeSupport := by
        by_contra h
        apply he
        apply Set.eq_univ_of_forall
        intro i
        by_contra hi
        exact h ⟨i,hi⟩
      obtain ⟨i,hi⟩ := hex
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

/-- Every actual boundary has zero full-negative-support components, in
every integer twist. -/
theorem coordinateLaurent_boundary_full_support_eq_zero (d : ℤ) (n : ℕ)
    (hc : Fintype.card σ = n+2)
    (t : coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n)
    (e : HomogeneousLaurentExponent σ d)
    (he : (e.liftedNegativeSupport : Set (ULift.{u} σ)) = Set.univ) :
    coordinateHomogeneousLaurentWeightComponent (R := R) d e (n+1)
      ((coordinateHomogeneousLaurentOrderedCechDifferential (R := R) d n).hom t) = 0 := by
  rw [coordinateHomogeneousLaurentWeightComponent_differential]
  have hz := LinearStudy.orderedCechSupport_eq_zero_of_full_support
    (coordinateCanonicalBaseRing R) e.liftedNegativeSupport he n
    (by simpa using Nat.lt_succ_self (n+1) |>.trans_le hc.ge)
    (coordinateHomogeneousLaurentWeightComponent (R := R) d e n t)
  rw [hz,map_zero]

/-- Exact top-boundary criterion for every integer twist of the actual
Laurent coordinate complex. -/
theorem coordinateLaurent_top_boundary_iff_full_support_zero (d : ℤ) (n : ℕ)
    (hc : Fintype.card σ = n+2)
    (s : coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d (n+1)) :
    (∃ t : coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n,
      (coordinateHomogeneousLaurentOrderedCechDifferential (R := R) d n).hom t = s) ↔
    ∀ e : HomogeneousLaurentExponent σ d,
      (e.liftedNegativeSupport : Set (ULift.{u} σ)) = Set.univ →
        coordinateHomogeneousLaurentWeightComponent (R := R) d e (n+1) s = 0 := by
  constructor
  · rintro ⟨t,rfl⟩ e he
    exact coordinateLaurent_boundary_full_support_eq_zero d n hc t e he
  · exact exists_preimage_coordinateLaurent_top_of_full_support_zero d n hc s
end MvPolynomial
