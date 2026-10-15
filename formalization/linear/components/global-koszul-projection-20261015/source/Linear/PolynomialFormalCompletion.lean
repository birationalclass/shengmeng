module
public import Linear.CompletionLocalization
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable (σ K : Type*) [Field K]

theorem polynomial_idealOfVars_eq_constantCoeff_kernel :
    MvPolynomial.idealOfVars σ K = RingHom.ker (MvPolynomial.constantCoeff (σ := σ) (R := K)) := by
  ext P
  rw [← pow_one (MvPolynomial.idealOfVars σ K), MvPolynomial.mem_pow_idealOfVars_iff']
  change (∀ x : σ →₀ ℕ, x.degree < 1 → P.coeff x = 0) ↔
    MvPolynomial.constantCoeff P = 0
  rw [MvPolynomial.constantCoeff_eq]
  constructor
  · intro h; exact h 0 (by simp)
  · intro h x hx
    have he : x = 0 := (Finsupp.degree_eq_zero_iff x).mp (by omega)
    simpa only [he] using h

theorem polynomial_idealOfVars_isMaximal : (MvPolynomial.idealOfVars σ K).IsMaximal := by
  rw [polynomial_idealOfVars_eq_constantCoeff_kernel]
  exact RingHom.ker_isMaximal_of_surjective _ (fun r => ⟨MvPolynomial.C r, by simp⟩)

attribute [local instance] polynomial_idealOfVars_isMaximal

def polynomialOriginFormalCompletionEquiv [Finite σ] :
    MvPowerSeries σ K ≃+* AdicCompletion
      (IsLocalRing.maximalIdeal (Localization.AtPrime (MvPolynomial.idealOfVars σ K)))
      (Localization.AtPrime (MvPolynomial.idealOfVars σ K)) :=
  (MvPowerSeries.toAdicCompletionAlgEquiv σ K).toRingEquiv.trans
    (completionLocalizationEquiv (MvPolynomial.idealOfVars σ K))

theorem polynomialOriginFormalCompletionEquiv_polynomial [Finite σ]
    (P : MvPolynomial σ K) :
    polynomialOriginFormalCompletionEquiv σ K P =
      AdicCompletion.of
        (IsLocalRing.maximalIdeal (Localization.AtPrime (MvPolynomial.idealOfVars σ K)))
        (Localization.AtPrime (MvPolynomial.idealOfVars σ K))
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime (MvPolynomial.idealOfVars σ K)) P) := by
  change completionLocalizationEquiv (MvPolynomial.idealOfVars σ K)
    (MvPowerSeries.toAdicCompletion σ K P) = _
  rw [MvPowerSeries.toAdicCompletion_coe, completionLocalizationEquiv_of]

end LinearStudy
