module
public import Linear.HomogeneousRationalPullback
public import Linear.ProjectiveChart
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
theorem affineChartPolynomialMap_eq_dehomogenize {K : Type*} [Field K] {n : ℕ}
    (H : MvPolynomial (Fin (n + 1)) K) :
    affineChartPolynomialMap H = affineDehomogenize H := by
  induction H using MvPolynomial.induction_on with
  | C a => simp [affineChartPolynomialMap, affineDehomogenize,
      MvPolynomial.finSuccEquiv_apply]
  | add H J hH hJ => simp [affineDehomogenize, map_add, hH, hJ]
  | mul_X H i hH =>
    rw [map_mul, hH]
    cases i using Fin.cases <;>
      simp [affineChartPolynomialMap, affineDehomogenize,
        MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]
end LinearStudy
