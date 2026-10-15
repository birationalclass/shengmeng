module
public import Linear.ProjectiveRegularCutOpen
public import Linear.FiniteCutPrimeCoordinates
public import Linear.ProjectiveCutOutsideExact
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

/-- EVERY prime of the original affine variety has an exact local Koszul
complex for a cut in a constructed nonempty open. At actual cut primes,
Artinianity and Nullstellensatz construct the actual smooth coordinates.
Outside the actual cut an original equation is a unit. No global CM or
pointwise exactness assumption is introduced. Global twisted sheaf
exactness and duality are not asserted by this local theorem. -/
theorem projectivePulledLinearSection_exists_localKoszul_exactAt_all_primes
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
          (∀ p : PrimeSpectrum (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal),
            let R := Localization.AtPrime p.asIdeal
            let H : Fin r → R := fun i => algebraMap (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) R
              (Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap
                (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i))))
            ∀ j : ℕ,0 < j →
              (koszulComplex (R := R) (M := Fin r → R) (Fintype.linearCombination R H)).ExactAt j) := by
  obtain ⟨c,hc,hex,hcuts⟩ := projectivePulledLinearSection_exists_finite_reduced_localKoszul_cuts
    f V hproper hq hf hV L hL hinj hfinite hdim x0 hx0
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  obtain ⟨hw0,hred,hfin,hiso,hsch,hlocal⟩ := hcuts w hw
  let I := (projectivePulledLinearSectionIdeal f V L w).map
    (affineChartPolynomialMap (K := ℂ)).toRingHom
  let C := MvPolynomial (Fin n) ℂ ⧸ I
  letI := hred
  letI := hfin
  letI : IsArtinianRing C := IsArtinianRing.of_finite ℂ C
  refine ⟨hw0,hred,hfin,hiso,hsch,?_⟩
  intro p
  let E : PrimeSpectrum (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) → Prop := fun p =>
    let R := Localization.AtPrime p.asIdeal
    let H : Fin r → R := fun i => algebraMap (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) R
      (Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap
        (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i))))
    ∀ j : ℕ,0 < j →
      (koszulComplex (R := R) (M := Fin r → R) (Fintype.linearCombination R H)).ExactAt j
  change E p
  by_cases hpI : I ≤ p.asIdeal.comap (Ideal.Quotient.mk V.affineIdeal)
  · obtain ⟨x,hx,hPk⟩ := artinian_polynomial_cut_prime_has_coordinates I
      (p.asIdeal.comap (Ideal.Quotient.mk V.affineIdeal)) hpI
    obtain ⟨hxV,_,hexact⟩ := hlocal x hx
    have hpoint : p=V.affinePoint x hxV := by
      apply PrimeSpectrum.ext
      apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk V.affineIdeal) Ideal.Quotient.mk_surjective
      change p.asIdeal.comap (Ideal.Quotient.mk V.affineIdeal)=
        (V.affinePointIdeal x).comap (Ideal.Quotient.mk V.affineIdeal)
      rw [V.affinePointIdeal_comap x hxV]
      exact hPk
    have hE : E (V.affinePoint x hxV) := hexact
    exact Eq.mpr (congrArg E hpoint) hE
  · exact projectivePulledLinearSection_localKoszul_exactAt_outside_cut f V L w p hpI

end LinearStudy
