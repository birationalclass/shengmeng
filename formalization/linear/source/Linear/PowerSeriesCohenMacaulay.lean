module
public import Linear.OriginRegular
public import Linear.ParameterLinearPart
public import Linear.PowerSeriesFlatten
/-! Actual Cohen–Macaulay property and dimension of formal coordinate rings,
derived from the regular coordinate sequence, height and depth. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
open RingTheory.Sequence

theorem localRing_CohenMacaulay_of_regular_maximal_generators
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (rs : List R) (hreg : IsRegular R rs)
    (hgen : Ideal.ofList rs = IsLocalRing.maximalIdeal R) :
    IsCohenMacaulayLocalRing R := by
  have hheight := Ideal.ofList_height_eq_length_of_isWeaklyRegular rs hreg.1
    (by rw [hgen]; exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top)
  have hdim : ringKrullDim R = (rs.length : WithBot ℕ∞) := by
    rw [hgen] at hheight
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hheight]
    rfl
  apply isCohenMacaulayLocalRing_of_ringKrullDim_le_depth R
  rw [hdim]
  apply WithBot.coe_le_coe.mpr
  rw [IsLocalRing.depth_eq_sSup_length_isRegular]
  apply le_sSup
  refine ⟨rs, ?_, ?_, rfl⟩
  · exact hreg
  · intro x hx
    rw [← hgen]
    exact Ideal.subset_span hx

theorem powerSeries_isCohenMacaulayLocalRing
    {K : Type*} [Field K] (n : ℕ) (hn : 0 < n) :
    IsCohenMacaulayLocalRing (MvPowerSeries (Fin n) K) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply localRing_CohenMacaulay_of_regular_maximal_generators
    (List.ofFn (MvPowerSeries.X (σ := Fin n) (R := K)))
    (powerSeries_variables_regular n)
  rw [show Ideal.ofList (List.ofFn (MvPowerSeries.X (σ := Fin n) (R := K))) =
      Ideal.span (Set.range (MvPowerSeries.X (σ := Fin n) (R := K))) by
    simp [Ideal.ofList, List.mem_ofFn, Set.range]]
  exact powerSeries_coordinateIdeal_eq_maximalIdeal

theorem powerSeries_ringKrullDim
    {K : Type*} [Field K] (n : ℕ) (hn : 0 < n) :
    ringKrullDim (MvPowerSeries (Fin n) K) = (n : WithBot ℕ∞) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let rs := List.ofFn (MvPowerSeries.X (σ := Fin n) (R := K))
  have hgen : Ideal.ofList rs = IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) K) := by
    rw [show Ideal.ofList rs = Ideal.span (Set.range (MvPowerSeries.X (σ := Fin n) (R := K))) by
      simp [rs, Ideal.ofList, List.mem_ofFn, Set.range]]
    exact powerSeries_coordinateIdeal_eq_maximalIdeal
  have hheight := Ideal.ofList_height_eq_length_of_isWeaklyRegular rs
    (powerSeries_variables_regular n).1
    (by rw [hgen]; exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top)
  rw [hgen] at hheight
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hheight]
  simp [rs]

theorem nestedPowerSeries_isCohenMacaulayLocalRing
    {K : Type*} [Field K] (r c : ℕ) (hn : 0 < r + c) :
    IsCohenMacaulayLocalRing (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K)) := by
  let : IsCohenMacaulayLocalRing (MvPowerSeries (Fin (r + c)) K) :=
    powerSeries_isCohenMacaulayLocalRing (r + c) hn
  exact isCohenMacaulayLocalRing_of_ringEquiv (nestedPowerSeriesEquiv K r c).symm

theorem nestedPowerSeries_ringKrullDim
    {K : Type*} [Field K] (r c : ℕ) (hn : 0 < r + c) :
    ringKrullDim (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K)) =
      (r + c : ℕ) := by
  rw [ringKrullDim_eq_of_ringEquiv (nestedPowerSeriesEquiv K r c)]
  exact powerSeries_ringKrullDim (r + c) hn

end LinearStudy
