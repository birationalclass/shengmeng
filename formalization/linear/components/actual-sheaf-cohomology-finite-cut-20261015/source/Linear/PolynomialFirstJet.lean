module
public import Linear.PolynomialFormalDerivative
public import Mathlib.RingTheory.MvPolynomial.Ideal
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K σ : Type*} [Field K]

/-- Zero constant and derivative constants characterize a polynomial with
no terms of total degree below two. -/
theorem polynomial_zero_firstJet_mem_vars_square
    (F : MvPolynomial σ K) (h0 : MvPolynomial.constantCoeff F = 0)
    (hD : ∀ j, MvPolynomial.constantCoeff (MvPolynomial.pderiv j F) = 0) :
    F ∈ (MvPolynomial.idealOfVars σ K) ^ 2 := by
  apply (MvPolynomial.mem_pow_idealOfVars_iff' 2 F).mpr
  intro d hd
  by_cases hz : d.degree = 0
  · have he : d = 0 := (Finsupp.degree_eq_zero_iff d).mp hz
    subst d
    simpa only [MvPolynomial.constantCoeff_eq] using h0
  · have hone : d.degree = 1 := by omega
    obtain ⟨j, hj⟩ := (Set.ext_iff.mp Finsupp.range_single_one d).mpr hone
    subst d
    have hh := hD j
    simpa [MvPolynomial.constantCoeff_eq, MvPolynomial.coeff_pderiv] using hh

/-- Pointwise vanishing of the polynomial and its derivatives gives actual
membership in the square of the original point ideal, before completion. -/
theorem polynomial_zero_firstJet_mem_point_square [Finite σ]
    (x : σ → K) (F : MvPolynomial σ K) (h0 : MvPolynomial.eval x F = 0)
    (hD : ∀ j, MvPolynomial.eval x (MvPolynomial.pderiv j F) = 0) :
    F ∈ (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom) ^ 2 := by
  let E := polynomialTranslation x
  have h0E : MvPolynomial.constantCoeff (E F) = 0 := by
    have h := polynomialTranslation_evaluation x 0 F
    simpa [MvPolynomial.eval_zero, E, h0] using h
  have hDE : ∀ j, MvPolynomial.constantCoeff (MvPolynomial.pderiv j (E F)) = 0 := by
    intro j
    rw [polynomialTranslation_pderiv]
    have h := polynomialTranslation_evaluation x 0 (MvPolynomial.pderiv j F)
    simpa [MvPolynomial.eval_zero, hD j] using h
  have hmem := polynomial_zero_firstJet_mem_vars_square (E F) h0E hDE
  have hmap : (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom).map E.toRingHom =
      MvPolynomial.idealOfVars σ K := by
    rw [← polynomialTranslation_origin_kernel x]
    exact Ideal.map_comap_of_surjective E.toRingHom E.surjective _
  have hpow : ((RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom) ^ 2).map E.toRingHom =
      (MvPolynomial.idealOfVars σ K) ^ 2 := by rw [Ideal.map_pow, hmap]
  rw [← hpow] at hmem
  exact (Ideal.apply_mem_of_equiv_iff (f := E.toRingEquiv)).mp hmem
end LinearStudy
