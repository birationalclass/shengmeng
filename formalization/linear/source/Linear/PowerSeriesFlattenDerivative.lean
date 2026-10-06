module
public import Linear.PowerSeriesFlatten
public import Mathlib.RingTheory.PowerSeries.Derivative
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K : Type*} [CommRing K]

theorem finSuccEquiv_pderiv_zero_coeff (n k : ℕ)
    (f : MvPowerSeries (Fin (n + 1)) K) :
    PowerSeries.coeff k (MvPowerSeries.finSuccEquiv K n (MvPowerSeries.pderiv 0 f)) =
      (k + 1) • PowerSeries.coeff (k + 1) (MvPowerSeries.finSuccEquiv K n f) := by
  classical
  ext d
  rw [MvPowerSeries.coeff_coeff_finSuccEquiv, MvPowerSeries.coeff_pderiv,
    map_nsmul, MvPowerSeries.coeff_coeff_finSuccEquiv]
  have hd : Finsupp.cons k d + Finsupp.single 0 1 = Finsupp.cons (k + 1) d := by
    ext i
    induction i using Fin.cases with
    | zero => simp
    | succ i => simp [Finsupp.single_apply]
  simp [hd, nsmul_eq_mul, mul_comm]

theorem finSuccEquiv_pderiv_succ_coeff (n k : ℕ) (j : Fin n)
    (f : MvPowerSeries (Fin (n + 1)) K) :
    PowerSeries.coeff k (MvPowerSeries.finSuccEquiv K n (MvPowerSeries.pderiv j.succ f)) =
      MvPowerSeries.pderiv j (PowerSeries.coeff k (MvPowerSeries.finSuccEquiv K n f)) := by
  classical
  ext d
  rw [MvPowerSeries.coeff_coeff_finSuccEquiv, MvPowerSeries.coeff_pderiv,
    MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_coeff_finSuccEquiv]
  have hd : Finsupp.cons k d + Finsupp.single j.succ 1 =
      Finsupp.cons k (d + Finsupp.single j 1) := by
    ext i
    induction i using Fin.cases with
    | zero => simp
    | succ i => simp [Finsupp.single_apply]
  simp [hd]

theorem powerSeriesMapEquiv_univariate_coeff {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (f : PowerSeries R) (k : ℕ) :
    PowerSeries.coeff k (powerSeriesMapEquiv e f) = e (PowerSeries.coeff k f) := by
  change PowerSeries.coeff k (PowerSeries.map e.toRingHom f) = _
  exact PowerSeries.coeff_map e.toRingHom k f

theorem nestedPowerSeriesEquiv_pderiv (r c : ℕ) (j : Fin c)
    (f : MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K)) :
    nestedPowerSeriesEquiv K r c (MvPowerSeries.pderiv j f) =
      MvPowerSeries.pderiv (normalVariableIndex r c j) (nestedPowerSeriesEquiv K r c f) := by
  induction c with
  | zero => exact Fin.elim0 j
  | succ c ih =>
    induction j using Fin.cases with
    | zero =>
      have hj : normalVariableIndex r (c + 1) 0 = 0 := by ext; rfl
      rw [hj]
      apply (MvPowerSeries.finSuccEquiv K (r + c)).injective
      apply PowerSeries.ext
      intro k
      refine Eq.trans ?_ (finSuccEquiv_pderiv_zero_coeff (K := K) (r + c) k
        (nestedPowerSeriesEquiv K r (c + 1) f)).symm
      change PowerSeries.coeff k ((MvPowerSeries.finSuccEquiv K (r + c))
        ((MvPowerSeries.finSuccEquiv K (r + c)).symm
          (powerSeriesMapEquiv (nestedPowerSeriesEquiv K r c)
            (MvPowerSeries.finSuccEquiv (MvPowerSeries (Fin r) K) c (MvPowerSeries.pderiv 0 f))))) = _
      rw [AlgEquiv.apply_symm_apply, powerSeriesMapEquiv_univariate_coeff,
        finSuccEquiv_pderiv_zero_coeff (K := MvPowerSeries (Fin r) K) c k, map_nsmul]
      change _ = (k + 1) • PowerSeries.coeff (k + 1)
        ((MvPowerSeries.finSuccEquiv K (r + c))
          ((MvPowerSeries.finSuccEquiv K (r + c)).symm
            (powerSeriesMapEquiv (nestedPowerSeriesEquiv K r c)
              (MvPowerSeries.finSuccEquiv (MvPowerSeries (Fin r) K) c f))))
      rw [AlgEquiv.apply_symm_apply, powerSeriesMapEquiv_univariate_coeff]
    | succ j =>
      have hj : normalVariableIndex r (c + 1) j.succ = (normalVariableIndex r c j).succ := by
        ext; rfl
      rw [hj]
      apply (MvPowerSeries.finSuccEquiv K (r + c)).injective
      apply PowerSeries.ext
      intro k
      refine Eq.trans ?_ (finSuccEquiv_pderiv_succ_coeff (K := K) (r + c) k
        (normalVariableIndex r c j) (nestedPowerSeriesEquiv K r (c + 1) f)).symm
      change PowerSeries.coeff k ((MvPowerSeries.finSuccEquiv K (r + c))
        ((MvPowerSeries.finSuccEquiv K (r + c)).symm
          (powerSeriesMapEquiv (nestedPowerSeriesEquiv K r c)
            (MvPowerSeries.finSuccEquiv (MvPowerSeries (Fin r) K) c (MvPowerSeries.pderiv j.succ f))))) = _
      rw [AlgEquiv.apply_symm_apply, powerSeriesMapEquiv_univariate_coeff,
        finSuccEquiv_pderiv_succ_coeff (K := MvPowerSeries (Fin r) K) c k j, ih]
      change _ = MvPowerSeries.pderiv (normalVariableIndex r c j)
        (PowerSeries.coeff k ((MvPowerSeries.finSuccEquiv K (r + c))
          ((MvPowerSeries.finSuccEquiv K (r + c)).symm
            (powerSeriesMapEquiv (nestedPowerSeriesEquiv K r c)
              (MvPowerSeries.finSuccEquiv (MvPowerSeries (Fin r) K) c f)))))
      rw [AlgEquiv.apply_symm_apply, powerSeriesMapEquiv_univariate_coeff]
end LinearStudy
