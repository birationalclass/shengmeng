module
public import Linear.PowerSeriesCoordinateChart
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K : Type*} [Field K] {r c : ℕ}

theorem powerSeries_retraction_coordinate_constantCoeff_zero
    (a : MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) →ₐ[MvPowerSeries (Fin r) K]
      MvPowerSeries (Fin r) K) (i : Fin c) :
    (a (MvPowerSeries.X i)).constantCoeff = 0 := by
  have hs : Function.Surjective a.toRingHom := by
    intro b
    exact ⟨MvPowerSeries.C b, a.commutes b⟩
  let : IsLocalHom a.toRingHom := IsLocalHom.of_surjective _ hs
  have hn : ¬ IsUnit (a (MvPowerSeries.X i)) := by
    intro hu
    have hu' := IsLocalHom.map_nonunit (f := a.toRingHom) (MvPowerSeries.X i) hu
    have := MvPowerSeries.isUnit_constantCoeff _ hu'
    simpa using this
  have hn' : ¬ IsUnit ((a (MvPowerSeries.X i)).constantCoeff) :=
    fun h => hn (MvPowerSeries.isUnit_iff_constantCoeff.mpr h)
  by_contra h
  exact hn' (isUnit_iff_ne_zero.mpr h)

def powerSeriesCentering
    (a : MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) →ₐ[MvPowerSeries (Fin r) K]
      MvPowerSeries (Fin r) K) :
    MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) ≃ₐ[MvPowerSeries (Fin r) K]
      MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) :=
  nestedPowerSeriesTranslation K r c (fun i => -a (MvPowerSeries.X i))
    (by intro i; simp [powerSeries_retraction_coordinate_constantCoeff_zero a i])

theorem powerSeriesCentering_coordinate_reduction_zero
    (a : MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) →ₐ[MvPowerSeries (Fin r) K]
      MvPowerSeries (Fin r) K) (i : Fin c) :
    a (powerSeriesCentering a (MvPowerSeries.X i)) = 0 := by
  change a (nestedPowerSeriesTranslation K r c (fun i => -a (MvPowerSeries.X i))
    (by intro i; simp [powerSeries_retraction_coordinate_constantCoeff_zero a i])
      (MvPowerSeries.X i)) = _
  rw [nestedPowerSeriesTranslation_X, map_add]
  have hc : a (MvPowerSeries.C (-a (MvPowerSeries.X i))) = -a (MvPowerSeries.X i) :=
    a.commutes _
  rw [hc, add_neg_cancel]

theorem powerSeriesCentering_pderiv
    (a : MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) →ₐ[MvPowerSeries (Fin r) K]
      MvPowerSeries (Fin r) K) (j : Fin c)
    (f : MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K)) :
    powerSeriesCentering a (MvPowerSeries.pderiv j f) =
      MvPowerSeries.pderiv j (powerSeriesCentering a f) :=
  nestedPowerSeriesTranslation_pderiv K r c _ _ j f

theorem powerSeriesCentering_symm_pderiv
    (a : MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) →ₐ[MvPowerSeries (Fin r) K]
      MvPowerSeries (Fin r) K) (j : Fin c)
    (f : MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K)) :
    (powerSeriesCentering a).symm (MvPowerSeries.pderiv j f) =
      MvPowerSeries.pderiv j ((powerSeriesCentering a).symm f) := by
  apply (powerSeriesCentering a).injective
  rw [AlgEquiv.apply_symm_apply, powerSeriesCentering_pderiv,
    AlgEquiv.apply_symm_apply]

theorem powerSeriesCentering_symm_jacobian
    (a : MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) →ₐ[MvPowerSeries (Fin r) K]
      MvPowerSeries (Fin r) K)
    (H : Fin c → MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K)) :
    (powerSeriesCentering a).symm
      (Matrix.det (fun i j => MvPowerSeries.pderiv j (H i))) =
      Matrix.det (fun i j => MvPowerSeries.pderiv j ((powerSeriesCentering a).symm (H i))) := by
  rw [AlgEquiv.map_det]
  congr 1
  funext i j
  exact powerSeriesCentering_symm_pderiv a j (H i)
end LinearStudy
