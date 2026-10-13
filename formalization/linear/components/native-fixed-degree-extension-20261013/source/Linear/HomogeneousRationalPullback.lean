module
public import Linear.ProjectiveRationalChart
public import Linear.ProjectiveIdealInvariance
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K σ : Type*} [Field K]

theorem homogeneous_aeval_smul {S : Type*} [CommRing S] [Algebra K S]
    {P : MvPolynomial σ K} {m : ℕ} (hP : P.IsHomogeneous m)
    (a : S) (v : σ → S) :
    MvPolynomial.aeval (fun i => a * v i) P = a ^ m * MvPolynomial.aeval v P := by
  classical
  induction hP using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add P Q hP hQ ihP ihQ => simp [ihP, ihQ, mul_add]
  | monomial d c hd =>
    have hdeg : (∑ i ∈ d.support, d i) = m := by
      simpa [Finsupp.weight, Finsupp.linearCombination_apply, Finsupp.sum] using hd
    simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_monomial,
      Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, hdeg]
    ring

def affineChartPolynomialMap {n : ℕ} :
    MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin n) K :=
  MvPolynomial.aeval (Fin.cases 1 MvPolynomial.X)

theorem affineChartPolynomialMap_comp_aeval {n : ℕ} {S : Type*}
    [CommRing S] [Algebra K S] (v : Fin n → S) :
    (MvPolynomial.aeval v).comp (affineChartPolynomialMap (K := K)) =
      MvPolynomial.aeval (Fin.cases 1 v) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases <;> simp [affineChartPolynomialMap]

theorem homogeneous_rational_chart_pullback {n : ℕ}
    (p0 : MvPolynomial (Fin n) K) (p : Fin n → MvPolynomial (Fin n) K)
    (H : MvPolynomial (Fin (n + 1)) K) {m : ℕ} (hH : H.IsHomogeneous m) :
    rationalPolynomialChartMap p0 p (affineChartPolynomialMap H) =
      (IsLocalization.Away.invSelf p0 (S := Localization.Away p0)) ^ m *
        MvPolynomial.aeval
          (Fin.cases (algebraMap _ (Localization.Away p0) p0)
            (fun i => algebraMap _ (Localization.Away p0) (p i))) H := by
  have he := affineChartPolynomialMap_comp_aeval
    (K := K) (fun i => algebraMap _ (Localization.Away p0) (p i) *
      IsLocalization.Away.invSelf p0)
  change MvPolynomial.aeval _ (affineChartPolynomialMap H) = _
  rw [← AlgHom.comp_apply, he]
  have hv : Fin.cases 1
      (fun i => algebraMap _ (Localization.Away p0) (p i) *
        IsLocalization.Away.invSelf p0) =
      (fun i => IsLocalization.Away.invSelf p0 *
        Fin.cases (algebraMap _ (Localization.Away p0) p0)
          (fun j => algebraMap _ (Localization.Away p0) (p j)) i) := by
    funext i
    cases i using Fin.cases with
    | zero =>
      simp only [Fin.cases_zero]
      rw [mul_comm]
      exact (IsLocalization.Away.mul_invSelf p0).symm
    | succ j => simp [mul_comm]
  rw [hv, homogeneous_aeval_smul hH]

end LinearStudy
