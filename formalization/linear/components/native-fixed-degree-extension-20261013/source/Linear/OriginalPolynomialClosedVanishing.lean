module
public import Linear.OriginalNonzeroPolynomialExtension
public import Linear.OriginalNormalizationNativeObjects
public import Linear.SchemeGlobalSectionPullbackVanishing
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual ORIGINAL polynomial extension preserves vanishing on any
family of actual subschemes, including every original point or fibre.
The uniform bound is chosen before the sections and the entire family.
Nonzero-section production remains an original4.2 obligation. -/
theorem originalProjectivePolynomial_eventually_nonzero_closed_vanishing {n : ℕ}
    (V : IntegralProjectiveEquations n) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    let B := homogeneousQuotientPiece V.ideal.toIdeal
    ∃ lower : ℕ, ∀ N : ℕ, lower ≤ N →
      ∀ (F : (Proj B).Modules) (j : F ⟶ originalProjectiveNativeTwist V N), Mono j →
      ∀ s : Γ(F,⊤), s ≠ 0 →
      ∀ (ι : Type*) (Z : ι → Scheme.{0}) (i : ∀ a, Z a ⟶ Proj B),
      (∀ a, (Scheme.Modules.pullback (i a)).map (moduleSheafGlobalSectionMorphism F s) = 0) →
      ∃ Q : CoordinateRing n, ∃ hQ : Q.IsHomogeneous N,
        originalProjectivePolynomialSection V N Q hQ = j.app ⊤ s ∧ Q ∉ V.ideal.toIdeal ∧
        ∀ a, (Scheme.Modules.pullback (i a)).map
          (moduleSheafGlobalSectionMorphism (originalProjectiveNativeTwist V N)
            (originalProjectivePolynomialSection V N Q hQ)) = 0 := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  obtain ⟨lower,hLift⟩ := originalProjectivePolynomial_eventually_nonzero_after_mono V
  refine ⟨lower,fun N hN F j hj s hs ι Z i hvanish => ?_⟩
  obtain ⟨Q,hQ,hEq,hNot⟩ := hLift N hN F j hj s hs
  refine ⟨Q,hQ,hEq,hNot,?_⟩
  intro a
  rw [hEq]
  exact moduleSheafGlobalSection_pullback_vanishing_after_map (i a) j s (hvanish a)
end LinearStudy
