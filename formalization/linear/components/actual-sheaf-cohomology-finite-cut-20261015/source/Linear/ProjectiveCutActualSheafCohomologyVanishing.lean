module
public import Linear.ProjectiveCutActualAllCohomologySupport
public import Linear.AffineKoszulActualSheafCohomologyVanishing
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] affineKoszulAllCohomologyConclusions
  affineKoszulActualHigherSheafCohomologyConclusions
open AlgebraicGeometry CategoryTheory
variable {n r : ℕ}

/-- For the SAME ORIGINAL pulled-linear cut,derive actual higher SHEAF
cohomology vanishing of ALL actual internal-Hom cohomology objects,EVERY
original coefficient N. Both original source exactness and finite cut are
DERIVED from the full original hypotheses. Outputs retain all previously
proved same-object geometric unit support. No CM/free/flat/FP/injectivity,
acyclicity/Ext/comparison certificate added. Global frames/epsilon and
canonical/proper-duality identifications remain separate open obligations. -/
theorem projectivePulledLinearSection_exists_actual_higherSheafCohomology_vanish
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hproper : V.ideal.toIdeal ≠ ⊥)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) = (r : WithBot ℕ∞))
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ c : MvPolynomial (Fin (r+1)) ℂ,c ≠ 0 ∧
      (∃ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0) ∧
      ∀ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0 →
        let I := (projectivePulledLinearSectionIdeal f V L w).map
          (affineChartPolynomialMap (K := ℂ)).toRingHom
        let C := MvPolynomial (Fin n) ℂ ⧸ I
        let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
        let H : Fin r → B := fun i => Ideal.Quotient.mk V.affineIdeal
          (affineChartPolynomialMap
            (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))
        w 0 ≠ 0 ∧ _root_.IsReduced C ∧ Module.Finite ℂ C ∧
          Nonempty (projectivePulledLinearSectionScheme f V L hL w ≅ Spec (CommRingCat.of C)) ∧
          AlgebraicGeometry.IsReduced (projectivePulledLinearSectionScheme f V L hL w) ∧
          ∃ he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination B H)).ExactAt j,
            affineKoszulAllCohomologyConclusions (CommRingCat.of B) r H ∧
              affineKoszulActualHigherSheafCohomologyConclusions (CommRingCat.of B) r H := by
  obtain ⟨c,hc,hex,hcuts⟩ := projectivePulledLinearSection_exists_actual_allCohomology_support
    f V hproper hq hf hV L hL hinj hfinite hdim x0 hx0
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  obtain ⟨hw0,hred,hfin,hiso,hsch,he,hprevious⟩ := hcuts w hw
  have hfinH := projectivePulledLinearSection_koszulQuotient_moduleFinite f V L w hfin
  refine ⟨hw0,hred,hfin,hiso,hsch,he,hprevious,?_⟩
  exact affineKoszulActualHigherSheafCohomologyConclusions_of_exact_fieldFinite ℂ _ _ _ he hfinH

end LinearStudy
