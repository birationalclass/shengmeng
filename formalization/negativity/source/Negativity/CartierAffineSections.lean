module

public import Negativity.CompleteCurveAffineAvoidance
public import Negativity.NormalizedCartierSigns
public import Negativity.NormalizedPrincipalInvariance
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Geometric section data for a Cartier divisor: actual effective divisors
in its linear system whose actual affine nonvanishing loci cover X.
These are the chart properties of projective coordinate sections over an
affine base. No degree or positivity condition is part of this structure.
The construction of these data from an actual projective embedding is a
separate geometric theorem, not asserted by this definition. -/
structure CartierAffineSectionCover
    {X : Scheme.{u}} [IsIntegral X] {ι : Type*}
    (A : CartierAtlas X ι) (σ : Type*) where
  multiplier : σ → X.functionFieldˣ
  effective : ∀ s, (A.rationalTwist (multiplier s)).Effective
  affine : ∀ s, IsAffineOpen (⟨(A.rationalTwist (multiplier s)).vanishingSupportᶜ,
    (cartierAtlas_vanishingSupport_isClosed X _).isOpen_compl⟩ : X.Opens)
  covers : ∀ x : X, ∃ s, x ∉ (A.rationalTwist (multiplier s)).vanishingSupport

/-- Final theorem: the actual affine nonvanishing-cover criterion implies
strictly positive actual Cartier intersection on every closed complete
integral curve. One coordinate section avoids the generic point; its
effective divisor must meet the curve because a complete curve cannot
be contained in an affine open. Principal invariance returns the degree
of the original Cartier divisor. No positive-degree hypothesis is used. -/
theorem complete_integral_curve_positive_of_affine_section_cover
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (j : C ⟶ X) [IsClosedImmersion j] {ι σ : Type*}
    (A : CartierAtlas X ι) (S : CartierAffineSectionCover A σ) :
    0 < normalizedCartierCurveIntersection hd k c j A := by
  classical
  obtain ⟨s, hs⟩ := S.covers (j (genericPoint C))
  let E := A.rationalTwist (S.multiplier s)
  let U : X.Opens := ⟨E.vanishingSupportᶜ,
    (cartierAtlas_vanishingSupport_isClosed X E).isOpen_compl⟩
  obtain ⟨x, hx⟩ := complete_integral_curve_meets_complement_affine_open
    hd k c j U (S.affine s)
  have hm : (j ⁻¹' E.vanishingSupport).Nonempty := by
    refine ⟨x, ?_⟩
    change j x ∈ E.vanishingSupport
    exact not_not.mp hx
  have hp := (complete_integral_curve_effective_cartier_intersection_signs
    hd k c j E (S.effective s) hs).2 hm
  rw [complete_integral_curve_ambient_cartier_principal_invariance hd k c j A
    (S.multiplier s)] at hp
  exact hp

end
end Negativity
