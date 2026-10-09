module
public import Linear.KoszulFunctionUnit
public import Linear.ProjectivePulledSectionAffineComparison
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n r : ℕ}

/-- At ANY prime of original V outside the actual cut, one original cut
equation is a unit. Its actual exterior-power Koszul complex is therefore
exact in every positive degree. No smoothness or global CM assumption. -/
theorem projectivePulledLinearSection_localKoszul_exactAt_outside_cut
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ)
    (p : PrimeSpectrum (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal))
    (hout : ¬ ((projectivePulledLinearSectionIdeal f V L w).map
        (affineChartPolynomialMap (K := ℂ)).toRingHom) ≤
          p.asIdeal.comap (Ideal.Quotient.mk V.affineIdeal)) :
    let R := Localization.AtPrime p.asIdeal
    let H : Fin r → R := fun i => algebraMap (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) R
      (Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap
        (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i))))
    ∀ j : ℕ,0 < j →
      (koszulComplex (R := R) (M := Fin r → R) (Fintype.linearCombination R H)).ExactAt j := by
  intro R H j hj
  have hex : ∃ i : Fin r,Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap
      (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i))) ∉ p.asIdeal := by
    by_contra hn
    push Not at hn
    apply hout
    rw [projectivePulledLinearSectionIdeal_map_affine]
    apply sup_le
    · intro F hF
      change Ideal.Quotient.mk V.affineIdeal F ∈ p.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hF]
      exact p.asIdeal.zero_mem
    · apply Ideal.span_le.mpr
      rintro F ⟨i,rfl⟩
      exact hn i
  obtain ⟨i,hi⟩ := hex
  have hu : IsUnit (H i) := (IsLocalization.AtPrime.isUnit_to_map_iff R p.asIdeal _).mpr hi
  exact functionKoszul_unit_exactAt H i hu j hj

end LinearStudy
