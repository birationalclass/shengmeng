module
public import Linear.OriginalFixedDegreeNonzeroExtension
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
attribute [local irreducible] originalNormalizationNativeDualSheaf

/-- The SAME constructed original polynomial degree precedes every sheaf,
identification, nonzero section and family of original pulled-back subschemes.
Vanishing of the given nonzero section is preserved by the actual extension.
Canonical identification remains an explicit UNVERIFIED input; proper/Koszul
production of that nonzero section is not assumed to have been proved. -/
theorem originalNormalizationDual_exists_fixed_degree_closed_extension
    {n r : ℕ} (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i, (L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    let B := homogeneousQuotientPiece V.ideal.toIdeal
    ∃ m : ℕ, 0 < m ∧
      ∀ (F : (Proj B).Modules)
        (canonicalIdentification : F ≅ originalNormalizationNativeDualSheaf V L hL),
      ∃ j : F ⟶ originalProjectiveNativeTwist V m, Mono j ∧
        (originalProjectiveNativeTwist V m).IsLocallyFree ∧
        (originalProjectiveNativeTwist V m).IsQuasicoherent ∧
        ∀ s : Γ(F,⊤), s ≠ 0 →
        ∀ (ι : Type*) (Z : ι → Scheme.{0}) (i : ∀ a, Z a ⟶ Proj B),
        (∀ a, (Scheme.Modules.pullback (i a)).map (moduleSheafGlobalSectionMorphism F s) = 0) →
        ∃ Q : CoordinateRing n, ∃ hQ : Q.IsHomogeneous m,
          originalProjectivePolynomialSection V m Q hQ = j.app ⊤ s ∧ Q ∉ V.ideal.toIdeal ∧
          ∀ a, (Scheme.Modules.pullback (i a)).map
            (moduleSheafGlobalSectionMorphism (originalProjectiveNativeTwist V m)
              (originalProjectivePolynomialSection V m Q hQ)) = 0 := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  obtain ⟨m,hm,hFixed⟩ :=
    originalNormalizationDual_exists_fixed_degree_nonzero_extension V L hL hinj hfinite
  refine ⟨m,hm,?_⟩
  intro F canonicalIdentification
  obtain ⟨j,hj,hfree,hqc,hLift⟩ := hFixed F canonicalIdentification
  refine ⟨j,hj,hfree,hqc,fun s hs ι Z i hvanish => ?_⟩
  obtain ⟨Q,hQ,hEq,hNot⟩ := hLift s hs
  refine ⟨Q,hQ,hEq,hNot,?_⟩
  intro a
  rw [hEq]
  exact moduleSheafGlobalSection_pullback_vanishing_after_map (i a) j s (hvanish a)
end LinearStudy
