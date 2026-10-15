module
public import Linear.ProjectivePulledWholeCutOriginalEmbedding
public import Linear.ProjectivePulledKoszulGlobalCokernelChartPushforward
public import Linear.SchemeModuleOriginalCutCokernelTarget
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading projectivePulledLinearKoszulForms
  nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm tildeKoszulOriginalCutCokernelCofork
  schemeModuleOriginalCutCokernelTargetIso
variable {n r : ℕ}

/-- From ORIGINAL f,V,L,x0 hypotheses,derive a NONEMPTY parameter open
BEFORE EVERY integer twist,on which the SAME NAMED ORIGINAL global
Koszul d1-cokernel is the WHOLE ORIGINAL cut structure sheaf pushed
along its SAME ACTUAL homogeneous quotient closed embedding into V.
Original chart comparison,whole-cut scheme iso and original map square
are all constructed,not assumed. This is an object comparison;native
cut line twist and geometric augmentation compatibility are separate. -/
theorem projectivePulledLinearSection_exists_globalCokernelWholeCutPushforwardIso
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
        ∀ k : ℤ,Nonempty (cokernel ((projectivePulledLinearKoszulComplex f V L hL w k).d 1 0) ≅
          (Scheme.Modules.pushforward (projectivePulledLinearSectionClosedEmbedding f V L hL w)).obj
            (SheafOfModules.unit (projectivePulledLinearSectionScheme f V L hL w).ringCatSheaf)) := by
  obtain ⟨cM,hcM,_,hgoodM⟩ := projectivePulledLinearSection_exists_globalCokernelChartPushforwardIso
    f V hq hf hV L hL hinj hfinite x0 hx0
  obtain ⟨cZ,hcZ,_,hgoodZ⟩ := projectivePulledLinearSection_exists_wholeCut_nativeChart_embedding_iso
    f V hq hf hV L hL hinj hfinite x0 hx0
  have hc : cM*cZ ≠ 0 := mul_ne_zero hcM hcZ
  have hex : ∃ w : Fin (r+1) → ℂ,MvPolynomial.eval w (cM*cZ) ≠ 0 := by
    by_contra h
    push Not at h
    apply hc
    apply MvPolynomial.funext
    intro w
    rw [map_zero]
    exact h w
  refine ⟨cM*cZ,hc,hex,?_⟩
  intro w hw
  rw [map_mul] at hw
  obtain ⟨hwM,hwZ⟩ := mul_ne_zero_iff.mp hw
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
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
  obtain ⟨g,hg⟩ := hgoodZ w hwZ
  let E := schemeModuleOriginalCutCokernelTargetIso R h j i g hg
  intro k
  obtain ⟨eM⟩ := hgoodM w hwM k
  exact ⟨eM ≪≫ E⟩

end LinearStudy