module
public import Linear.OriginalNormalizationNativeEmbeddingAbove
public import Linear.OriginalNonzeroPolynomialExtension
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

/-- One ORIGINAL positive degree is fixed before ALL sheaves, their
identifications and nonzero sections. The actual above-bound embedding
and original polynomial extension are proved. Canonical identification
remains an EXPLICIT UNVERIFIED geometric input, as authorized by the user.
Original4.2 nonzero-section production and all-iterate vanishing remain open. -/
theorem originalNormalizationDual_exists_fixed_degree_nonzero_extension
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
            ∃ Q : CoordinateRing n, ∃ hQ : Q.IsHomogeneous m,
              originalProjectivePolynomialSection V m Q hQ = j.app ⊤ s ∧
              Q ∉ V.ideal.toIdeal := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  obtain ⟨lower,hLift⟩ := originalProjectivePolynomial_eventually_nonzero_after_mono V
  obtain ⟨m,hbound,hm,nativeMap,hmono,hfree,hqc⟩ :=
    originalNormalizationNativeDual_exists_embedding_above V L hL hinj hfinite lower
  letI : Mono nativeMap := hmono
  refine ⟨m,hm,?_⟩
  intro F canonicalIdentification
  let j := canonicalIdentification.hom ≫ nativeMap
  letI hj : Mono j := inferInstance
  refine ⟨j,hj,hfree,hqc,?_⟩
  intro s hs
  exact hLift m hbound F j hj s hs
end LinearStudy
