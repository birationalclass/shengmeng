module
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
/-!
# The linear part of arbitrary parameter generators

If n power series generate the maximal ideal of K[[s_1,...,s_n]],
their actual derivative matrix at zero has invertible determinant.
This derives a prerequisite for the new parameter-base construction;
it does not assert a formal inverse or finite flatness over that new base.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem parameter_generator_constantCoeff_zero
    (T : ι → MvPowerSeries ι K)
    (hT : Ideal.span (Set.range T) = IsLocalRing.maximalIdeal (MvPowerSeries ι K))
    (i : ι) : (T i).constantCoeff = 0 := by
  have hm : T i ∈ IsLocalRing.maximalIdeal (MvPowerSeries ι K) := by
    rw [← hT]
    exact Ideal.mem_span_range_self
  change ¬ IsUnit (T i) at hm
  by_contra h
  exact hm (MvPowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr h))

theorem parameter_generators_jacobian_constantCoeff_unit
    (T : ι → MvPowerSeries ι K)
    (hT : Ideal.span (Set.range T) = IsLocalRing.maximalIdeal (MvPowerSeries ι K)) :
    IsUnit (Matrix.det (fun i j => (MvPowerSeries.pderiv j (T i)).constantCoeff)) := by
  have hx (i : ι) : MvPowerSeries.X (R := K) i ∈ Ideal.span (Set.range T) := by
    rw [hT]
    change ¬ IsUnit (MvPowerSeries.X (R := K) i)
    simp [MvPowerSeries.isUnit_iff_constantCoeff]
  choose C hC using fun i => Ideal.mem_span_range_iff_exists_fun.mp (hx i)
  let C0 : Matrix ι ι K := fun i j => (C i j).constantCoeff
  let J : Matrix ι ι K := fun i j => (MvPowerSeries.pderiv j (T i)).constantCoeff
  have hinv : C0 * J = 1 := by
    ext i j
    have hd := congrArg (fun f : MvPowerSeries ι K =>
      (MvPowerSeries.pderiv j f).constantCoeff) (hC i)
    have hprod (k : ι) : (MvPowerSeries.pderiv j (C i k * T k)).constantCoeff =
        (C i k).constantCoeff * (MvPowerSeries.pderiv j (T k)).constantCoeff := by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
        parameter_generator_constantCoeff_zero T hT k, zero_mul, add_zero]
    have hsum : (MvPowerSeries.pderiv j (∑ k, C i k * T k)).constantCoeff =
        ∑ k, (C i k).constantCoeff * (MvPowerSeries.pderiv j (T k)).constantCoeff := by
      rw [map_sum, map_sum]
      exact Finset.sum_congr rfl (fun k hk => hprod k)
    rw [hsum] at hd
    change (∑ k, (C i k).constantCoeff * (MvPowerSeries.pderiv j (T k)).constantCoeff) = _
    rw [hd]
    by_cases h : i = j
    · subst j
      simp
    · rw [MvPowerSeries.pderiv_X_of_ne h]
      simp [Matrix.one_apply, h]
  have hd := congrArg Matrix.det hinv
  rw [Matrix.det_mul, Matrix.det_one] at hd
  apply isUnit_iff_ne_zero.mpr
  intro hz
  change Matrix.det J = 0 at hz
  rw [hz, mul_zero] at hd
  exact zero_ne_one hd
end LinearStudy
