module

public import Linear.PowerSeriesSpecialization
public import Mathlib.RingTheory.Regular.Flat

/-!
# Regular equations remain regular on the actual closed fiber

In a Noetherian local ring, exchange a regular equation sequence with a
sequence regular on its quotient. Apply this to the parameter variables,
whose regularity on the equation quotient follows from flatness over the
parameter ring. The explicit specialization quotient equivalence then
proves regularity of the specialized equations. Zero constant terms are
derived from regularity of the original equations, not assumed separately.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open RingTheory.Sequence
namespace LinearStudy
variable {R : Type*} [CommRing R]

theorem ofList_smul_top (H : List R) :
    (Ideal.ofList H • (⊤ : Submodule R R)) = Ideal.ofList H := by
  exact Ideal.mul_top _

theorem weaklyRegular_quotient_iff (H P : List R) :
    IsWeaklyRegular (R ⧸ Ideal.ofList H) (P.map (Ideal.Quotient.mk (Ideal.ofList H))) ↔
      IsWeaklyRegular (R ⧸ (Ideal.ofList H • (⊤ : Submodule R R))) P := by
  rw [ofList_smul_top]
  exact isWeaklyRegular_map_algebraMap_iff (R := R) (S := R ⧸ Ideal.ofList H)
    (M := R ⧸ Ideal.ofList H) P

theorem weaklyRegular_exchange [IsLocalRing R] [IsNoetherianRing R]
    (H P : List R) (hH : IsRegular R H)
    (hPm : ∀ p ∈ P, p ∈ IsLocalRing.maximalIdeal R)
    (hP : IsWeaklyRegular (R ⧸ Ideal.ofList H)
      (P.map (Ideal.Quotient.mk (Ideal.ofList H)))) :
    IsWeaklyRegular (R ⧸ Ideal.ofList P)
      (H.map (Ideal.Quotient.mk (Ideal.ofList P))) := by
  have hweak : IsWeaklyRegular R (H ++ P) :=
    (isWeaklyRegular_append_iff R H P).mpr
      ⟨hH.toIsWeaklyRegular, (weaklyRegular_quotient_iff H P).mp hP⟩
  have hproper : Ideal.ofList H ≠ ⊤ := by
    intro ht
    apply hH.top_ne_smul
    rw [ht, Submodule.top_smul]
  have hmem : ∀ x ∈ H ++ P, x ∈ IsLocalRing.maximalIdeal R := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact IsLocalRing.le_maximalIdeal hproper (Ideal.subset_span hx)
    · exact hPm x hx
  have hreg := IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal R hmem hweak
  have hswap := IsLocalRing.isRegular_of_perm hreg (List.perm_append_comm (l₁ := H) (l₂ := P))
  exact (weaklyRegular_quotient_iff P H).mpr
    ((isWeaklyRegular_append_iff R P H).mp hswap.toIsWeaklyRegular).2

theorem weaklyRegular_transport_ringEquiv {S : Type*} [CommRing S]
    (e : R ≃+* S) (rs : List R) :
    IsWeaklyRegular R rs ↔ IsWeaklyRegular S (rs.map e) := by
  apply e.toAddEquiv.isWeaklyRegular_congr
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro r hr x
  exact e.map_mul r x

theorem powerSeries_specialized_equations_weaklyRegular
    {K : Type*} [Field K] {r c : ℕ}
    (H : Fin c → MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K))
    (hH : IsRegular (MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K))
      (List.ofFn H))
    [Module.Flat (MvPowerSeries (Fin (r + 1)) K)
      (MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K) ⧸ Ideal.span (Set.range H))] :
    IsWeaklyRegular (MvPowerSeries (Fin c) K)
      (List.ofFn (fun i => parameterSpecialization (H i))) := by
  let B := MvPowerSeries (Fin (r + 1)) K
  let S := MvPowerSeries (Fin c) B
  let P : List S := List.ofFn (fun i : Fin (r + 1) => MvPowerSeries.C (MvPowerSeries.X i))
  let A := S ⧸ Ideal.span (Set.range H)
  have hP : IsWeaklyRegular A
      (P.map (Ideal.Quotient.mk (Ideal.span (Set.range H)))) := by
    have hp := (powerSeries_variables_regular (R := K) (r + 1)).toIsWeaklyRegular.of_flat
      (S := A)
    have hBA : ∀ b : B, algebraMap B A b =
        Ideal.Quotient.mk (Ideal.span (Set.range H)) (MvPowerSeries.C b) := by
      intro b
      change Ideal.Quotient.mk _ (algebraMap B S b) = _
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self]
      rfl
    rw [List.map_ofFn] at hp
    have hfun : (fun i : Fin (r + 1) => algebraMap B A (MvPowerSeries.X i)) =
        (fun i => Ideal.Quotient.mk (Ideal.span (Set.range H))
          (MvPowerSeries.C (MvPowerSeries.X i))) := by
      funext i
      exact hBA _
    change IsWeaklyRegular A (List.ofFn (fun i => algebraMap B A (MvPowerSeries.X i))) at hp
    rw [hfun] at hp
    dsimp only [P]
    rw [List.map_ofFn]
    exact hp
  have hPm : ∀ p ∈ P, p ∈ IsLocalRing.maximalIdeal S := by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    change ¬ IsUnit (MvPowerSeries.C (σ := Fin c) (MvPowerSeries.X (R := K) i))
    simp [MvPowerSeries.isUnit_iff_constantCoeff]
  have hP' : IsWeaklyRegular (S ⧸ Ideal.ofList (List.ofFn H))
      (P.map (Ideal.Quotient.mk (Ideal.ofList (List.ofFn H)))) := by
    rw [ideal_ofFn]
    exact hP
  have hx := weaklyRegular_exchange (List.ofFn H) P hH hPm hP'
  have hi : Ideal.ofList P = Ideal.span (Set.range (fun i : Fin (r + 1) =>
      MvPowerSeries.C (σ := Fin c) (MvPowerSeries.X (R := K) i))) := ideal_ofFn _
  let e : (S ⧸ Ideal.ofList P) ≃+* MvPowerSeries (Fin c) K :=
    (Ideal.quotEquivOfEq hi).trans parameterSpecializationQuotientEquiv
  have he : ∀ z : S, e (Ideal.Quotient.mk _ z) = parameterSpecialization z := by
    intro z
    rfl
  have hy := (weaklyRegular_transport_ringEquiv e _).mp hx
  rw [List.map_map, List.map_ofFn] at hy
  have hh : (fun i => (e ∘ Ideal.Quotient.mk (Ideal.ofList P)) (H i)) =
      (fun i => parameterSpecialization (H i)) := by
    funext i
    exact he (H i)
  change IsWeaklyRegular (MvPowerSeries (Fin c) K)
    (List.ofFn (fun i => (e ∘ Ideal.Quotient.mk (Ideal.ofList P)) (H i))) at hy
  rw [hh] at hy
  exact hy

theorem powerSeries_specialized_equations_zeroConstant
    {K : Type*} [Field K] {r c : ℕ}
    (H : Fin c → MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K))
    (hH : IsRegular (MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K))
      (List.ofFn H)) :
    ∀ i, (parameterSpecialization (H i)).constantCoeff = 0 := by
  have hproper : Ideal.span (Set.range H) ≠ ⊤ := by
    intro ht
    apply hH.top_ne_smul
    rw [ideal_ofFn, ht, Submodule.top_smul]
  intro i
  have hm := IsLocalRing.le_maximalIdeal hproper (Ideal.subset_span (Set.mem_range_self i))
  change ¬ IsUnit (H i) at hm
  rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.isUnit_iff_constantCoeff,
    isUnit_iff_ne_zero, not_not] at hm
  change (MvPowerSeries.map MvPowerSeries.constantCoeff (H i)).constantCoeff = 0
  rw [MvPowerSeries.constantCoeff_map]
  exact hm

theorem powerSeries_specialized_equations_regular
    {K : Type*} [Field K] {r c : ℕ}
    (H : Fin c → MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K))
    (hH : IsRegular (MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K))
      (List.ofFn H))
    [Module.Flat (MvPowerSeries (Fin (r + 1)) K)
      (MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K) ⧸ Ideal.span (Set.range H))] :
    IsRegular (MvPowerSeries (Fin c) K)
      (List.ofFn (fun i => parameterSpecialization (H i))) := by
  apply IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal (MvPowerSeries (Fin c) K)
  · intro h hh
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hh
    change ¬ IsUnit (parameterSpecialization (H i))
    rw [MvPowerSeries.isUnit_iff_constantCoeff,
      powerSeries_specialized_equations_zeroConstant H hH i]
    exact not_isUnit_zero
  · exact powerSeries_specialized_equations_weaklyRegular H hH

end LinearStudy
