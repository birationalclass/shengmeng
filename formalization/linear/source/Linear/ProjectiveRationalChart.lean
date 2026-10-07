module
public import Linear.PolynomialFormalDerivative
public import Mathlib.RingTheory.Localization.Away.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K σ : Type*} [Field K]

/-- Actual rational coordinate pullback into the open set where p0 is invertible. -/
def rationalPolynomialChartMap (p0 : MvPolynomial σ K) (p : σ → MvPolynomial σ K) :
    MvPolynomial σ K →ₐ[K] Localization.Away p0 :=
  MvPolynomial.aeval (fun i => algebraMap _ (Localization.Away p0) (p i) *
    IsLocalization.Away.invSelf p0)

def polynomialAwayPointEvaluation (x : σ → K) (p0 : MvPolynomial σ K)
    (hp0 : MvPolynomial.eval x p0 ≠ 0) : Localization.Away p0 →ₐ[K] K :=
  IsLocalization.Away.liftAlgHom p0
    (f := MvPolynomial.aeval (R := K) x) (isUnit_iff_ne_zero.mpr hp0)

theorem polynomialAwayPointEvaluation_algebraMap (x : σ → K) (p0 : MvPolynomial σ K)
    (hp0 : MvPolynomial.eval x p0 ≠ 0) (a : MvPolynomial σ K) :
    polynomialAwayPointEvaluation x p0 hp0 (algebraMap _ (Localization.Away p0) a) =
      MvPolynomial.eval x a := by
  simp [polynomialAwayPointEvaluation]

theorem polynomialAwayPointEvaluation_invSelf (x : σ → K) (p0 : MvPolynomial σ K)
    (hp0 : MvPolynomial.eval x p0 ≠ 0) :
    polynomialAwayPointEvaluation x p0 hp0 (IsLocalization.Away.invSelf p0) =
      (MvPolynomial.eval x p0)⁻¹ := by
  apply mul_left_cancel₀ hp0
  rw [mul_inv_cancel₀ hp0]
  have h := congrArg (polynomialAwayPointEvaluation x p0 hp0)
    (IsLocalization.Away.mul_invSelf (S := Localization.Away p0) p0)
  simpa only [map_mul, map_one, polynomialAwayPointEvaluation_algebraMap] using h

theorem rationalPolynomialChartMap_point_evaluation
    (x : σ → K) (p0 : MvPolynomial σ K) (hp0 : MvPolynomial.eval x p0 ≠ 0)
    (p : σ → MvPolynomial σ K) :
    (polynomialAwayPointEvaluation x p0 hp0).comp (rationalPolynomialChartMap p0 p) =
      MvPolynomial.aeval (fun i => MvPolynomial.eval x (p i) / MvPolynomial.eval x p0) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [rationalPolynomialChartMap, polynomialAwayPointEvaluation_algebraMap,
    polynomialAwayPointEvaluation_invSelf, div_eq_mul_inv]

theorem rationalPolynomialChartMap_point_kernel
    (x : σ → K) (p0 : MvPolynomial σ K) (hp0 : MvPolynomial.eval x p0 ≠ 0)
    (p : σ → MvPolynomial σ K) :
    RingHom.ker (MvPolynomial.aeval (R := K)
      (fun i => MvPolynomial.eval x (p i) / MvPolynomial.eval x p0)).toRingHom =
      (RingHom.ker (polynomialAwayPointEvaluation x p0 hp0).toRingHom).comap
        (rationalPolynomialChartMap p0 p).toRingHom := by
  rw [RingHom.comap_ker]
  exact congrArg (fun f : MvPolynomial σ K →ₐ[K] K => RingHom.ker f.toRingHom)
    (rationalPolynomialChartMap_point_evaluation x p0 hp0 p).symm
end LinearStudy
