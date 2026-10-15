module
public import Linear.ProjectivePulledNativeChartCutEmbedding
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading
variable {n r : ℕ}

/-- ORIGINAL geometric hypotheses derive a NONEMPTY parameter open on
which the ACTUAL native chart cut is the WHOLE original projective cut
OVER the SAME original V. Neither coverage nor the desired map square
is an added original hypothesis. Original ideals and nilpotents retained. -/
theorem projectivePulledLinearSection_exists_wholeCut_nativeChart_embedding_iso
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
        letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
        let a := Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)
        let ha : a ∈ homogeneousQuotientPiece V.ideal.toIdeal 1 :=
          ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩
        let R := Away (homogeneousQuotientPiece V.ideal.toIdeal) a
        let h : Fin r → R := fun i => Away.mk (homogeneousQuotientPiece V.ideal.toIdeal) ha f.degree
          (projectivePulledLinearKoszulForms f V L w i)
          (by simpa using projectivePulledLinearKoszulForms_homogeneous f V L hL w i)
        ∃ g : Spec (CommRingCat.of (R ⧸ Ideal.span (Set.range h))) ≅
            projectivePulledLinearSectionScheme f V L hL w,
          g.hom ≫ projectivePulledLinearSectionClosedEmbedding f V L hL w =
            Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range h)))) ≫
              Proj.awayι (homogeneousQuotientPiece V.ideal.toIdeal) a ha one_pos := by
  obtain ⟨c,hc,hex,hgood⟩ := projectivePulledLinearSection_exists_native_open_coverage
    f V hq hf hV L hL hinj hfinite x0 hx0
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  exact projectivePulledLinearSection_nativeChart_exists_embedding_iso f V L hL w (hgood w hw).1

end LinearStudy