module
public import Linear.OriginalFixedDegreeClosedVanishing
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

/-- Construct the original finite linear normalization and ONE degree from
the ORIGINAL V alone. No affine-chart point, normalization, embedding or
polynomial-lifting certificate is an input. The canonical identification and
the actual nonzero section with its actual vanishing remain explicit inputs.
This does NOT prove the original canonical identification or Lemma4.2. -/
theorem originalVariety_exists_fixed_degree_nonzero_closed_extension {n : ℕ}
    (V : IntegralProjectiveEquations n) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    let B := homogeneousQuotientPiece V.ideal.toIdeal
    ∃ r : ℕ, r ≤ n ∧ ∃ L : Fin (r+1) → CoordinateRing n,
    ∃ hL : ∀ a, (L a).IsHomogeneous 1,
      Function.Injective (projectiveLinearNormalizationMap V L) ∧
      (projectiveLinearNormalizationMap V L).Finite ∧
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
  obtain ⟨r,P,hr,hP,hDegree,hHilbert,L,hL,hinj,hfinite,hDim,hNoBasePoint⟩ :=
    projective_exists_linear_normalization V
  obtain ⟨m,hm,hFixed⟩ :=
    originalNormalizationDual_exists_fixed_degree_closed_extension V L hL hinj hfinite
  exact ⟨r,hr,L,hL,hinj,hfinite,m,hm,hFixed⟩
end LinearStudy
