module
public import Linear.NativeKoszulSupportedCokernelUnit
public import Linear.ProjectivePulledKoszulOriginalAmbientCover
public import Linear.ProjectivePulledLinearKoszulGlobal
public import Linear.HomogeneousQuotientKoszulAffineCounit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading projectivePulledLinearKoszulForms
  nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm
variable {n r : ℕ}

/-- Derive a NONEMPTY original parameter open BEFORE all integer twists
on which the ACTUAL restriction-adjunction unit of the SAME named original
GLOBAL Koszul cokernel is an isomorphism. Actual ambient coverage and
actual off-cut cokernel vanishing are DERIVED;neither is a new input.
No nonzero defining-ideal or dimension hypothesis is needed for this
support/gluing statement. Whole original cut-map identification is separate. -/
theorem projectivePulledLinearSection_exists_globalCokernelRestrictionUnit_isIso
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
        let j := Proj.awayι (homogeneousQuotientPiece V.ideal.toIdeal) a ha one_pos
        ∀ k : ℤ,IsIso ((Scheme.Modules.restrictAdjunction j).unit.app
          (cokernel ((projectivePulledLinearKoszulComplex f V L hL w k).d 1 0))) := by
  obtain ⟨c,hc,hex,hcover⟩ := projectivePulledLinearSection_exists_original_ambient_cover
    f V hq hf hV L hL hinj hfinite x0 hx0
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  dsimp only
  intro k
  unfold projectivePulledLinearKoszulComplex
  exact nativeProjectiveKoszul_cokernelRestrictionUnit_isIso
    (homogeneousQuotientPiece V.ideal.toIdeal)
    (fun t : Fin (n+1) => Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X t))
    (fun t => ⟨MvPolynomial.X t,MvPolynomial.isHomogeneous_X ℂ t,rfl⟩)
    (homogeneousQuotient_coordinate_adjoin_eq_top V.ideal.toIdeal)
    (projectivePulledLinearKoszulForms f V L w)
    (projectivePulledLinearKoszulForms_homogeneous f V L hL w) k
    (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0))
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩ (hcover w hw)

end LinearStudy
