module
public import Linear.HomogeneousQuotientKoszulAffineCounit
public import Linear.ProjectivePulledNativeChartCutEmbedding
public import Linear.SchemeModuleOriginalCutNativeTwistTarget
public import Linear.NativeIntegerTwistWholeChartFrame
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
  tildeKoszulOriginalCutCokernelCofork schemeModuleOriginalCutNativeTwistTargetIso
  nativeIntegerTwistWholeSheafIsoOfBasicOpenTop CategoryTheory.Functor.mapHomologicalComplex
variable {n r : ℕ}

/-- Identify the LITERAL original chart quotient with the WHOLE original
cut's native integer twist, using the original closed-embedding square
and coordinate-power frame. This construction does not mention a mapped
Koszul presentation or depend on its large nested data type. -/
def projectivePulledKoszulWholeCutLiteralTargetIso
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ)
    (htop : let J := projectivePulledLinearSectionIdeal f V L w
      letI := homogeneousQuotientGrading J (projectivePulledLinearSectionIdeal_isHomogeneous f V L hL w)
      Proj.basicOpen (homogeneousQuotientPiece J) (Ideal.Quotient.mk J (MvPolynomial.X 0)) = ⊤) :
    let J := projectivePulledLinearSectionIdeal f V L w
    let hJ := projectivePulledLinearSectionIdeal_isHomogeneous f V L hL w
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    letI := homogeneousQuotientGrading J hJ
    let a := Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)
    let ha : a ∈ homogeneousQuotientPiece V.ideal.toIdeal 1 :=
      ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩
    let R := CommRingCat.of (HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal) a)
    let h : Fin r → R := fun t => HomogeneousLocalization.Away.mk
      (homogeneousQuotientPiece V.ideal.toIdeal) ha f.degree
      (projectivePulledLinearKoszulForms f V L w t)
      (by simpa using projectivePulledLinearKoszulForms_homogeneous f V L hL w t)
    (Scheme.Modules.pushforward (Proj.awayι (homogeneousQuotientPiece V.ideal.toIdeal) a ha one_pos)).obj
      (tildeKoszulOriginalCutCokernelCofork R h).pt ≅
        (Scheme.Modules.pushforward (projectivePulledLinearSectionClosedEmbedding f V L hL w)).obj
          (nativeProjectiveModuleSheaf (homogeneousQuotientPiece J)
            (nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece J))
            (nativeProjectiveRingIntegerPiece_graded (homogeneousQuotientPiece J)) k) := by
  let J := projectivePulledLinearSectionIdeal f V L w
  let hJ := projectivePulledLinearSectionIdeal_isHomogeneous f V L hL w
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI := homogeneousQuotientGrading J hJ
  let a := Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)
  let ha : a ∈ homogeneousQuotientPiece V.ideal.toIdeal 1 :=
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩
  let R := CommRingCat.of (HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal) a)
  let h : Fin r → R := fun i => HomogeneousLocalization.Away.mk
    (homogeneousQuotientPiece V.ideal.toIdeal) ha f.degree
    (projectivePulledLinearKoszulForms f V L w i)
    (by simpa using projectivePulledLinearKoszulForms_homogeneous f V L hL w i)
  let j := Proj.awayι (homogeneousQuotientPiece V.ideal.toIdeal) a ha one_pos
  let i := projectivePulledLinearSectionClosedEmbedding f V L hL w
  let hwhole := projectivePulledLinearSection_nativeChart_exists_embedding_iso f V L hL w htop
  let g := Classical.choose hwhole
  let hg := Classical.choose_spec hwhole
  let tau := nativeIntegerTwistWholeSheafIsoOfBasicOpenTop (homogeneousQuotientPiece J)
    (Ideal.Quotient.mk J (MvPolynomial.X 0))
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩ htop k
  exact schemeModuleOriginalCutNativeTwistTargetIso R h j i g hg
    (tildeKoszulOriginalCutCokernelCofork R h).pt rfl _ tau

end LinearStudy
