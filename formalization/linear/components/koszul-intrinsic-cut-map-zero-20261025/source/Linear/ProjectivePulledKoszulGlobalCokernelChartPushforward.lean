module
public import Linear.NativeKoszulGlobalCokernelChartPushforward
public import Linear.ProjectivePulledKoszulSupportedCokernelUnit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading projectivePulledLinearKoszulForms
  nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm
  nativeProjectiveKoszulGlobalCokernelChartPushforwardIso tildeKoszulOriginalCutCokernelCofork
variable {n r : ℕ}

/-- On a derived NONEMPTY original parameter open chosen BEFORE EVERY
integer twist,the SAME named original GLOBAL d1-cokernel is isomorphic
to the ACTUAL pushforward from the main chart of the SAME original affine
cut structure sheaf. Original ambient coverage,off-cut vanishing,unit
invertibility and chart comparison are all DERIVED. The separately defined
WHOLE projective cut's embedding and native twist comparison remain OPEN. -/
theorem projectivePulledLinearSection_exists_globalCokernelChartPushforwardIso
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
        let R := CommRingCat.of (HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal) a)
        let j := Proj.awayι (homogeneousQuotientPiece V.ideal.toIdeal) a ha one_pos
        let h : Fin r → R := fun i => HomogeneousLocalization.Away.mk
          (homogeneousQuotientPiece V.ideal.toIdeal) ha f.degree
          (projectivePulledLinearKoszulForms f V L w i)
          (by simpa using projectivePulledLinearKoszulForms_homogeneous f V L hL w i)
        ∀ k : ℤ,Nonempty (cokernel ((projectivePulledLinearKoszulComplex f V L hL w k).d 1 0) ≅
          (Scheme.Modules.pushforward j).obj (tildeKoszulOriginalCutCokernelCofork R h).pt) := by
  obtain ⟨c,hc,hex,hcover⟩ := projectivePulledLinearSection_exists_original_ambient_cover
    f V hq hf hV L hL hinj hfinite x0 hx0
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  dsimp only
  intro k
  refine ⟨?_⟩
  unfold projectivePulledLinearKoszulComplex
  exact nativeProjectiveKoszulGlobalCokernelChartPushforwardIso
    (homogeneousQuotientPiece V.ideal.toIdeal)
    (fun t : Fin (n+1) => Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X t))
    (fun t => ⟨MvPolynomial.X t,MvPolynomial.isHomogeneous_X ℂ t,rfl⟩)
    (homogeneousQuotient_coordinate_adjoin_eq_top_unlifted V.ideal.toIdeal)
    (projectivePulledLinearKoszulForms f V L w)
    (projectivePulledLinearKoszulForms_homogeneous f V L hL w) k
    (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0))
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩ (hcover w hw)

end LinearStudy
