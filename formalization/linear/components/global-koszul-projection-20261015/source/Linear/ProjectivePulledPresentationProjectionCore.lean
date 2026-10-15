module
public import Linear.NativeKoszulPresentationGlobalProjectionExistsProof
public import Linear.ProjectivePulledKoszulSupportedCokernelUnit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading projectivePulledLinearKoszulForms
  nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm
  nativeProjectiveKoszulMappedPresentationData CategoryTheory.Functor.mapHomologicalComplex
variable {n r : ℕ}

/-- The ACTUAL original ambient cover statement,not a proof or certificate. -/
def projectivePulledLinearKoszulAmbientCover (f : HomogeneousEndomorphism n)
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (w : Fin (r+1) → ℂ) : Prop :=
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  ∀ x : Proj (homogeneousQuotientPiece V.ideal.toIdeal),
    x ∈ Proj.basicOpen (homogeneousQuotientPiece V.ideal.toIdeal)
      (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)) ∨
    ∃ i : Fin r,x ∈ Proj.basicOpen (homogeneousQuotientPiece V.ideal.toIdeal)
      (projectivePulledLinearKoszulForms f V L w i)

/-- ORIGINAL hypotheses DERIVE this exact named cover on a nonempty
parameter open. No nonzero defining-ideal/dimension premise is added. -/
theorem projectivePulledLinearSection_exists_presentationAmbientCover
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ c : MvPolynomial (Fin (r+1)) ℂ,c ≠ 0 ∧
      (∃ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0) ∧
      ∀ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0 →
        projectivePulledLinearKoszulAmbientCover f V L w := by
  simpa only [projectivePulledLinearKoszulAmbientCover] using
    projectivePulledLinearSection_exists_original_ambient_cover
      f V hq hf hV L hL hinj hfinite x0 hx0

/-- ACTUAL original-geometry projection proof term. The coverage input
is DERIVED by the preceding theorem and the final family theorem.
Its inferred proposition must be independently audited. -/
def projectivePulledLinearKoszulGlobalProjectionExistsProof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ)
    (hc : projectivePulledLinearKoszulAmbientCover f V L w) :=
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  nativeProjectiveKoszulPresentationGlobalProjectionExistsProof
    (homogeneousQuotientPiece V.ideal.toIdeal)
    (fun t : Fin (n+1) => Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X t))
    (fun t => ⟨MvPolynomial.X t,MvPolynomial.isHomogeneous_X ℂ t,rfl⟩)
    (homogeneousQuotient_coordinate_adjoin_eq_top V.ideal.toIdeal)
    (projectivePulledLinearKoszulForms f V L w)
    (projectivePulledLinearKoszulForms_homogeneous f V L hL w) k
    (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0))
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩ hc

end LinearStudy
