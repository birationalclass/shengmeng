module
public import Linear.PowerSeriesCohenMacaulay
public import Linear.PowerSeriesThickeningReduction
public import Linear.PowerSeriesThickeningFinite
public import Linear.RegularGeneratorsFree
public import Linear.RegularSpecialization
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace LinearStudy
open RingTheory.Sequence
variable {K : Type*} [Field K]
attribute [local instance] NoZeroDivisors.to_isDomain

theorem powerSeries_coordinateIdeal_height {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (c : ℕ) (hc : 0 < c) :
    (Ideal.span (Set.range (MvPowerSeries.X (σ := Fin c) (R := R)))).height = c := by
  let : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
  have hlist : Ideal.ofList (List.ofFn (MvPowerSeries.X (σ := Fin c) (R := R))) =
      Ideal.span (Set.range (MvPowerSeries.X (σ := Fin c) (R := R))) := by
    simp [Ideal.ofList, List.mem_ofFn, Set.range]
  have hp : (Ideal.span (Set.range (MvPowerSeries.X (σ := Fin c) (R := R)))).IsPrime := by
    rw [← powerSeries_constantCoeff_kernel]
    exact RingHom.ker_isPrime MvPowerSeries.constantCoeff
  have hh := Ideal.ofList_height_eq_length_of_isWeaklyRegular _
    (powerSeries_variables_regular c).1 (by rw [hlist]; exact hp.ne_top)
  simpa only [hlist, List.length_ofFn, Fintype.card_fin] using hh

theorem nestedPowerSeries_maximalIdeal (r c : ℕ) (hr : 0 < r) (hc : 0 < c) :
    IsLocalRing.maximalIdeal (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K)) =
      Ideal.span (Set.range (MvPowerSeries.X (σ := Fin c) (R := MvPowerSeries (Fin r) K))) ⊔
      Ideal.span (Set.range (fun i : Fin r =>
        MvPowerSeries.C (σ := Fin c) (MvPowerSeries.X (R := K) i))) := by
  let : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  let : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
  let B := MvPowerSeries (Fin r) K
  let R := MvPowerSeries (Fin c) B
  let P : Ideal R := Ideal.span (Set.range (fun i : Fin r => MvPowerSeries.C (MvPowerSeries.X i)))
  let cc : R →+* B := MvPowerSeries.constantCoeff
  have hmap : P.map cc = IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_span, ← Set.range_comp]
    change Ideal.span (Set.range (fun i : Fin r =>
      MvPowerSeries.constantCoeff (MvPowerSeries.C (MvPowerSeries.X i) : R))) = _
    simp only [MvPowerSeries.constantCoeff_C]
    exact powerSeries_coordinateIdeal_eq_maximalIdeal
  have hcomap : (IsLocalRing.maximalIdeal B).comap cc = IsLocalRing.maximalIdeal R := by
    ext f
    change ¬ IsUnit (MvPowerSeries.constantCoeff f) ↔ ¬ IsUnit f
    exact not_congr (MvPowerSeries.isUnit_iff_constantCoeff (φ := f)).symm
  rw [← hcomap, ← hmap, Ideal.comap_map_of_surjective cc
    (fun b => ⟨MvPowerSeries.C b, MvPowerSeries.constantCoeff_C b⟩)]
  rw [← RingHom.ker_eq_comap_bot, powerSeries_constantCoeff_kernel, sup_comm]

theorem powerSeries_thickening_equations_regular
    (r c : ℕ) (hc : 0 < c)
    (H : Fin c → MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K))
    (e : ℕ) (he : 0 < e)
    (hupper : Ideal.span (Set.range H) ≤
      Ideal.span (Set.range (MvPowerSeries.X (σ := Fin c) (R := MvPowerSeries (Fin r) K))))
    (hlower : (Ideal.span (Set.range (MvPowerSeries.X (σ := Fin c)
      (R := MvPowerSeries (Fin r) K)))) ^ e ≤ Ideal.span (Set.range H)) :
    IsRegular (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K)) (List.ofFn H) := by
  let : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
  let R := MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K)
  let I := Ideal.span (Set.range H)
  let J : Ideal R := Ideal.span (Set.range MvPowerSeries.X)
  let : IsCohenMacaulayLocalRing R := nestedPowerSeries_isCohenMacaulayLocalRing r c (by omega)
  have hrad : I.radical = J := powerSeries_thickening_radical I e he hupper hlower
  have hheight : I.height = c := by
    rw [Ideal.height_eq_inf_minimalPrimes, ← Ideal.radical_minimalPrimes,
      hrad, ← Ideal.height_eq_inf_minimalPrimes]
    exact powerSeries_coordinateIdeal_height c hc
  apply isRegular_of_ofList_height_eq_length_of_isCohenMacaulayLocalRing
  · intro x hx
    have hxI : x ∈ I := Ideal.subset_span (by simpa [List.mem_ofFn] using hx)
    have hxJ := hupper hxI
    apply (Ideal.span_le.mpr (fun z hz => ?_) : J ≤ IsLocalRing.maximalIdeal R) hxJ
    obtain ⟨i, rfl⟩ := hz
    change ¬ IsUnit (MvPowerSeries.X i : R)
    simp [MvPowerSeries.isUnit_iff_constantCoeff]
  · rw [show Ideal.ofList (List.ofFn H) = I by simp [I, Ideal.ofList, List.mem_ofFn, Set.range]]
    simpa only [List.length_ofFn, Fintype.card_fin] using hheight

end LinearStudy
