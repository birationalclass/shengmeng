module
public import Linear.ProjectiveVarietyLocalCutRegular
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2600000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
open AlgebraicGeometry CategoryTheory RingTheory.Sequence
variable {n r : ℕ}

/-- The nonempty open is constructed from original f,V and the SAME
finite normalization. Every actual affine cut point has the original
equations regular in the original variety local ring, hence its actual
exterior-power Koszul complex is exact in every positive degree. This
does not yet assert global twisted sheaf exactness or proper duality. -/
theorem projectivePulledLinearSection_exists_finite_reduced_localKoszul_cuts
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hproper : V.ideal.toIdeal ≠ ⊥)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet=V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)=(r : WithBot ℕ∞))
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ c : MvPolynomial (Fin (r+1)) ℂ,c ≠ 0 ∧
      (∃ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0) ∧
      ∀ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0 →
        let I := (projectivePulledLinearSectionIdeal f V L w).map
          (affineChartPolynomialMap (K := ℂ)).toRingHom
        let C := MvPolynomial (Fin n) ℂ ⧸ I
        w 0 ≠ 0 ∧ _root_.IsReduced C ∧ Module.Finite ℂ C ∧
          Nonempty (projectivePulledLinearSectionScheme f V L hL w ≅ Spec (CommRingCat.of C)) ∧
          AlgebraicGeometry.IsReduced (projectivePulledLinearSectionScheme f V L hL w) ∧
          (∀ x : Fin n → ℂ,x ∈ MvPolynomial.zeroLocus ℂ I →
            ∃ hx : normalizedProjectivePoint x ∈ V.zeroSet,
              let p := (V.affinePoint x hx).asIdeal
              let R := Localization.AtPrime p
              let H : Fin r → R := fun i => algebraMap (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) R
                (Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap
                  (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i))))
              IsRegular R (List.ofFn H) ∧
                ∀ j : ℕ,0 < j →
                  (koszulComplex (R := R) (M := Fin r → R) (Fintype.linearCombination R H)).ExactAt j) := by
  obtain ⟨c,hc,hex,hcuts⟩ := projectivePulledLinearSection_exists_smooth_finite_reduced_cuts
    f V hq hf hV L hL hinj hfinite x0 hx0
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  obtain ⟨hw0,hred,hfin,hiso,hsch,hsmooth⟩ := hcuts w hw
  letI := hred
  letI := hfin
  refine ⟨hw0,hred,hfin,hiso,hsch,?_⟩
  intro x hx
  obtain ⟨hxV,hs⟩ := hsmooth x hx
  refine ⟨hxV,?_⟩
  exact ⟨projectivePulledLinearSection_regular_in_variety_localRing
      f V hproper L w hdim x hxV hs hx,
    projectivePulledLinearSection_localKoszul_exactAt_smooth_cut_point
      f V hproper L w hdim x hxV hs hx⟩

end LinearStudy
