module
public import Linear.ProjectiveRationalChart
public import Linear.SmoothProjectiveFormalSocle
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K σ : Type*} [Field K]

def formalPolynomialAtPointAlg (x : σ → K) :
    MvPolynomial σ K →ₐ[K] MvPowerSeries σ K where
  __ := formalPolynomialAtPoint x
  commutes' a := formalPolynomialAtPoint_C x a

def polynomialAwayFormalMap (x : σ → K) (p0 : MvPolynomial σ K)
    (hp0 : MvPolynomial.eval x p0 ≠ 0) :
    Localization.Away p0 →ₐ[K] MvPowerSeries σ K :=
  IsLocalization.Away.liftAlgHom p0 (f := formalPolynomialAtPointAlg x)
    (show IsUnit (formalPolynomialAtPoint x p0) from by
      rw [MvPowerSeries.isUnit_iff_constantCoeff, formalPolynomialAtPoint_constantCoeff]
      exact isUnit_iff_ne_zero.mpr hp0)

theorem polynomialAwayFormalMap_algebraMap (x : σ → K) (p0 : MvPolynomial σ K)
    (hp0 : MvPolynomial.eval x p0 ≠ 0) (a : MvPolynomial σ K) :
    polynomialAwayFormalMap x p0 hp0 (algebraMap _ (Localization.Away p0) a) =
      formalPolynomialAtPoint x a := by
  simp [polynomialAwayFormalMap, formalPolynomialAtPointAlg]

theorem polynomialAwayFormalMap_invSelf [Finite σ] (x : σ → K) (p0 : MvPolynomial σ K)
    (hp0 : MvPolynomial.eval x p0 ≠ 0) :
    polynomialAwayFormalMap x p0 hp0 (IsLocalization.Away.invSelf p0) =
      ((formalPolynomialAtPointUnit x p0 hp0)⁻¹ : (MvPowerSeries σ K)ˣ) := by
  apply (formalPolynomialAtPointUnit x p0 hp0).isUnit.mul_left_cancel
  have h := congrArg (polynomialAwayFormalMap x p0 hp0)
    (IsLocalization.Away.mul_invSelf (S := Localization.Away p0) p0)
  simpa only [map_mul, map_one, polynomialAwayFormalMap_algebraMap,
    ← formalPolynomialAtPointUnit_coe x p0 hp0, Units.mul_inv] using h

theorem rationalPolynomialChartMap_formal_comparison
    {r c : ℕ} (x : Fin r ⊕ Fin c → ℂ)
    (p0 : MvPolynomial (Fin r ⊕ Fin c) ℂ) (hp0 : MvPolynomial.eval x p0 ≠ 0)
    (p : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ) :
    (polynomialAwayFormalMap x p0 hp0).comp (rationalPolynomialChartMap p0 p) =
      MvPolynomial.aeval (projectiveFormalCoordinateRatios x p0 hp0 p) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [rationalPolynomialChartMap, projectiveFormalCoordinateRatios,
    polynomialAwayFormalMap_algebraMap, polynomialAwayFormalMap_invSelf, mul_comm]

theorem polynomialAwayFormalMap_constantCoeff (x : σ → K) (p0 : MvPolynomial σ K)
    (hp0 : MvPolynomial.eval x p0 ≠ 0) :
    MvPowerSeries.constantCoeff.comp (polynomialAwayFormalMap x p0 hp0).toRingHom =
      (polynomialAwayPointEvaluation x p0 hp0).toRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers p0)
  apply RingHom.ext
  intro a
  change (polynomialAwayFormalMap x p0 hp0
    (algebraMap _ (Localization.Away p0) a)).constantCoeff =
      polynomialAwayPointEvaluation x p0 hp0 (algebraMap _ (Localization.Away p0) a)
  simp only [polynomialAwayFormalMap_algebraMap,
    formalPolynomialAtPoint_constantCoeff, polynomialAwayPointEvaluation_algebraMap]

theorem polynomialAwayFormalMap_isUnit_iff (x : σ → K) (p0 : MvPolynomial σ K)
    (hp0 : MvPolynomial.eval x p0 ≠ 0) (a : Localization.Away p0) :
    IsUnit (polynomialAwayFormalMap x p0 hp0 a) ↔
      polynomialAwayPointEvaluation x p0 hp0 a ≠ 0 := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff]
  have h := RingHom.congr_fun (polynomialAwayFormalMap_constantCoeff x p0 hp0) a
  change (polynomialAwayFormalMap x p0 hp0 a).constantCoeff = _ at h
  rw [h, isUnit_iff_ne_zero]
  rfl

theorem rationalPolynomialChartMap_formal_isUnit_iff
    (x : σ → K) (p0 : MvPolynomial σ K) (hp0 : MvPolynomial.eval x p0 ≠ 0)
    (p : σ → MvPolynomial σ K) (H : MvPolynomial σ K) :
    IsUnit (polynomialAwayFormalMap x p0 hp0 (rationalPolynomialChartMap p0 p H)) ↔
      MvPolynomial.eval
        (fun i => MvPolynomial.eval x (p i) / MvPolynomial.eval x p0) H ≠ 0 := by
  rw [polynomialAwayFormalMap_isUnit_iff]
  have h := AlgHom.congr_fun (rationalPolynomialChartMap_point_evaluation x p0 hp0 p) H
  change polynomialAwayPointEvaluation x p0 hp0 (rationalPolynomialChartMap p0 p H) = _ at h
  rw [h]
  rfl

theorem rationalPolynomialChartMap_target_local_generators
    (x : σ → K) (p0 : MvPolynomial σ K) (hp0 : MvPolynomial.eval x p0 ≠ 0)
    (p : σ → MvPolynomial σ K) (I Q : Ideal (MvPolynomial σ K)) [Q.IsPrime]
    (hQ : Q = RingHom.ker (MvPolynomial.aeval (R := K)
      (fun i => MvPolynomial.eval x (p i) / MvPolynomial.eval x p0)).toRingHom)
    {ι : Type*} (H : ι → MvPolynomial σ K)
    (hlocal : I.map (algebraMap _ (Localization.AtPrime Q)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime Q) (H i)))) :
    (I.map (rationalPolynomialChartMap p0 p).toRingHom).map
      (polynomialAwayFormalMap x p0 hp0).toRingHom =
        Ideal.span (Set.range (fun i =>
          polynomialAwayFormalMap x p0 hp0 (rationalPolynomialChartMap p0 p (H i)))) := by
  rw [Ideal.map_map]
  apply local_ideal_generators_image I Q H
  · intro a
    apply (rationalPolynomialChartMap_formal_isUnit_iff x p0 hp0 p a).mpr
    have ha : (a : MvPolynomial σ K) ∉ Q := a.property
    intro hz
    apply ha
    exact (congrArg (fun J : Ideal (MvPolynomial σ K) =>
      (a : MvPolynomial σ K) ∈ J) hQ).mpr hz
  · exact hlocal

end LinearStudy
