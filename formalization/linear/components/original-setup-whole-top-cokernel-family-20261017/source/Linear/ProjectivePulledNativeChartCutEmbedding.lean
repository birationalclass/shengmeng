module
public import Linear.ProjectivePulledNativeChartCutQuotientFactor
public import Linear.SchemeSpecOriginalQuotientFactorSquare
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

/-- Under explicit WHOLE-cut native-chart coverage,the ACTUAL original
quotient-cut spectrum is isomorphic to the WHOLE original projective cut
OVER the ORIGINAL V. The desired map square is PROVED from original ring
naturality and native Proj.awayι_comp_map,not assumed or replaced by an
abstract scheme isomorphism. Coverage is derived in the original wrapper. -/
theorem projectivePulledLinearSection_nativeChart_exists_embedding_iso
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ)
    (htop : let J := projectivePulledLinearSectionIdeal f V L w
      letI := homogeneousQuotientGrading J (projectivePulledLinearSectionIdeal_isHomogeneous f V L hL w)
      Proj.basicOpen (homogeneousQuotientPiece J) (Ideal.Quotient.mk J (MvPolynomial.X 0)) = ⊤) :
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
  let J := projectivePulledLinearSectionIdeal f V L w
  let hJ := projectivePulledLinearSectionIdeal_isHomogeneous f V L hL w
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI := homogeneousQuotientGrading J hJ
  let a := Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)
  let ha : a ∈ homogeneousQuotientPiece V.ideal.toIdeal 1 :=
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩
  let R := Away (homogeneousQuotientPiece V.ideal.toIdeal) a
  let h : Fin r → R := fun i => Away.mk (homogeneousQuotientPiece V.ideal.toIdeal) ha f.degree
    (projectivePulledLinearKoszulForms f V L w i)
    (by simpa using projectivePulledLinearKoszulForms_homogeneous f V L hL w i)
  let aJ := Ideal.Quotient.mk J (MvPolynomial.X 0)
  let haJ : aJ ∈ homogeneousQuotientPiece J 1 :=
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩
  let jJ := Proj.awayι (homogeneousQuotientPiece J) aJ haJ one_pos
  letI : IsIso jJ := isIso_of_isOpenImmersion_of_opensRange_eq_top jJ
    ((Proj.opensRange_awayι (homogeneousQuotientPiece J) aJ haJ one_pos).trans htop)
  obtain ⟨e,he⟩ := projectivePulledLinearSection_nativeChart_exists_quotient_factor_equiv f V L hL w
  let g : Spec (CommRingCat.of (R ⧸ Ideal.span (Set.range h))) ≅
      projectivePulledLinearSectionScheme f V L hL w :=
    (Scheme.Spec.mapIso e.symm.toCommRingCatIso.op).trans (asIso jJ)
  refine ⟨g,?_⟩
  change (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
    Proj.awayι (homogeneousQuotientPiece J) aJ haJ one_pos) ≫
      homogeneousQuotientClosedEmbedding V.ideal.toIdeal J V.ideal.isHomogeneous hJ le_sup_left = _
  have hsquare : Proj.awayι (homogeneousQuotientPiece J) aJ haJ one_pos ≫
      homogeneousQuotientClosedEmbedding V.ideal.toIdeal J V.ideal.isHomogeneous hJ le_sup_left =
    Spec.map (CommRingCat.ofHom (Away.map
      (homogeneousQuotientFactorGraded V.ideal.toIdeal J le_sup_left) a)) ≫
        Proj.awayι (homogeneousQuotientPiece V.ideal.toIdeal) a ha one_pos :=
    homogeneousQuotientClosedEmbedding_away_square V.ideal.toIdeal J V.ideal.isHomogeneous hJ le_sup_left
  rw [Category.assoc,hsquare]
  rw [← Category.assoc,schemeSpec_originalQuotientFactor_square _ e _ he]

end LinearStudy