module
public import Linear.ProjectiveCutAffineKoszul
public import Linear.ProjectiveCutKoszulQuotient
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2600000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
open AlgebraicGeometry CategoryTheory
variable {n r : ℕ}

/-- The original pulled linear cut has a constructed actual affine
projective resolution: its exterior-power Koszul complex, its natural quotient
augmentation, and the derived positive exactness. The quotient is naturally
the actual cut ring by projectivePulledLinearSection_koszulQuotientAlgEquiv.
Global twisted sheaves and canonical duality are not asserted. -/
theorem projectivePulledLinearSection_exists_actual_affineKoszul_resolution
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
        let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
        let H : Fin r → B := fun i => Ideal.Quotient.mk V.affineIdeal
          (affineChartPolynomialMap
            (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))
        w 0 ≠ 0 ∧ _root_.IsReduced C ∧ Module.Finite ℂ C ∧
          Nonempty (projectivePulledLinearSectionScheme f V L hL w ≅ Spec (CommRingCat.of C)) ∧
          AlgebraicGeometry.IsReduced (projectivePulledLinearSectionScheme f V L hL w) ∧
          (∀ j : ℕ,0 < j →
            (koszulComplex (Fintype.linearCombination B H)).ExactAt j) ∧
          QuasiIso (functionKoszulAugmentationMap H) ∧
          ∃ P : ProjectiveResolution (ModuleCat.of B (B ⧸ Ideal.span (Set.range H))),
            P.complex=koszulComplex (Fintype.linearCombination B H) := by
  obtain ⟨c,hc,hex,hcuts⟩ := projectivePulledLinearSection_exists_affineKoszul_exactAt
    f V hproper hq hf hV L hL hinj hfinite hdim x0 hx0
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  obtain ⟨hw0,hred,hfin,hiso,hsch,hexact⟩ := hcuts w hw
  refine ⟨hw0,hred,hfin,hiso,hsch,hexact,?_,?_⟩
  · exact functionKoszulAugmentation_quasiIso_of_exact _ hexact
  · exact ⟨functionKoszulResolutionOfExact _ hexact,rfl⟩

end LinearStudy
