/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
module
public import Linear.ProjectiveLaurentWeightAssembly
public import Linear.ProjectiveLaurentDegreeThreshold
public import Linear.OrderedCechSupportAlternating
/- Minimal original Laurent boundary proof extended above the canonical threshold, from AINTLIB at
ab1451487da02cd4483d0e2cdb2cc9e44bbbac17. No hyperplane divisor model,
finite homology claims or unverified geometric comparison is imported. -/
@[expose] public section
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
local instance coordinateLaurentThresholdBoundaryDecidableEq : DecidableEq σ := Classical.decEq σ
/-- Every positive-degree cocycle in the homogeneous Laurent presentation of the ordered Cech
complex for every ORIGINAL integer twist above -card(sigma) is a boundary. -/
theorem exists_preimage_coordinateHomogeneousLaurentOrderedCechDifferential_of_gt_neg_card
    [Fintype σ] [LinearOrder σ] (d : ℤ) (hd : -(Fintype.card σ:ℤ)<d) (n : ℕ)
    (s : coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d (n + 1))
    (hs : (coordinateHomogeneousLaurentOrderedCechDifferential
      (R := R) (σ := σ) d (n + 1)).hom s = 0) :
    ∃ t : coordinateHomogeneousLaurentOrderedCechObject
        (R := R) (σ := σ) d n,
      (coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d n).hom t = s := by
  classical
  have hcomponent_cycle (e : HomogeneousLaurentExponent σ d) :
      LinearStudy.orderedCechSupportDifferential
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          e.liftedNegativeSupport (n + 1)
          (coordinateHomogeneousLaurentWeightComponent
            (R := R) d e (n + 1) s) = 0 := by
    rw [← coordinateHomogeneousLaurentWeightComponent_differential
      (R := R) (σ := σ) (d := d) (e := e) (n := n + 1), hs]
    exact map_zero
      (coordinateHomogeneousLaurentWeightComponent (R := R) d e (n + 2))
  have hpreimage (e : HomogeneousLaurentExponent σ d) :
      ∃ t : LinearStudy.OrderedCechSupportCochain
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          e.liftedNegativeSupport n,
        LinearStudy.orderedCechSupportDifferential
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            e.liftedNegativeSupport n t =
          coordinateHomogeneousLaurentWeightComponent
            (R := R) d e (n + 1) s := by
    obtain ⟨i, hi⟩ := e.exists_not_mem_liftedNegativeSupport_of_gt_neg_card hd
    exact LinearStudy.exists_preimage_orderedCechSupportDifferential
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      e.liftedNegativeSupport i hi n
      (coordinateHomogeneousLaurentWeightComponent (R := R) d e (n + 1) s)
      (hcomponent_cycle e)
  choose t ht using hpreimage
  refine ⟨∑ e ∈ coordinateHomogeneousLaurentActiveWeights d (n + 1) s,
    coordinateHomogeneousLaurentWeightInclusion (R := R) d e n (t e), ?_⟩
  rw [map_sum]
  calc
    (∑ e ∈ coordinateHomogeneousLaurentActiveWeights d (n + 1) s,
        (coordinateHomogeneousLaurentOrderedCechDifferential
          (R := R) (σ := σ) d n).hom
          (coordinateHomogeneousLaurentWeightInclusion (R := R) d e n (t e))) =
      ∑ e ∈ coordinateHomogeneousLaurentActiveWeights d (n + 1) s,
        coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
          (LinearStudy.orderedCechSupportDifferential
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            e.liftedNegativeSupport n (t e)) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [coordinateHomogeneousLaurentWeightInclusion_differential]
    _ = ∑ e ∈ coordinateHomogeneousLaurentActiveWeights d (n + 1) s,
        coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
          (coordinateHomogeneousLaurentWeightComponent
            (R := R) d e (n + 1) s) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [ht e]
    _ = s := coordinateHomogeneousLaurentActiveWeights_reconstruct d (n + 1) s
end
end MvPolynomial
