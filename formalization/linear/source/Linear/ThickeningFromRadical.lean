module
public import Linear.PowerSeriesThickeningFlat
public import Linear.ArbitraryParameterSocle
public import Mathlib.RingTheory.Finiteness.Ideal
/-! Derive the full regular finite flat structure from the actual radical
condition and apply the audited relative Jacobian theorem with its constructed
reduction map, including all admissible arbitrary parameter lifts. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] NoZeroDivisors.to_isDomain

theorem powerSeries_radical_coordinate_sandwich
    {R σ : Type*} [CommRing R] [IsNoetherianRing R]
    [Fintype σ] [DecidableEq σ]
    (I : Ideal (MvPowerSeries σ R))
    (hrad : I.radical = Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))) :
    ∃ e : ℕ, 0 < e ∧
      I ≤ Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R))) ∧
      (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))) ^ e ≤ I := by
  obtain ⟨n, hn⟩ := I.exists_radical_pow_le_of_fg (IsNoetherian.noetherian _)
  refine ⟨n + 1, Nat.zero_lt_succ _, ?_, ?_⟩
  · rw [← hrad]
    exact Ideal.le_radical
  · rw [← hrad]
    exact (Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn

theorem powerSeries_thickening_structure_from_radical
    {K : Type*} [Field K] (r c : ℕ) (hr : 0 < r) (hc : 0 < c)
    (H : Fin c → MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K))
    (hrad : (Ideal.span (Set.range H)).radical =
      Ideal.span (Set.range (MvPowerSeries.X (σ := Fin c) (R := MvPowerSeries (Fin r) K)))) :
    RingTheory.Sequence.IsRegular
      (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K)) (List.ofFn H) ∧
    Module.Finite (MvPowerSeries (Fin r) K)
      (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) ⧸ Ideal.span (Set.range H)) ∧
    Module.Free (MvPowerSeries (Fin r) K)
      (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) ⧸ Ideal.span (Set.range H)) := by
  let : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
  obtain ⟨e, he, hupper, hlower⟩ := powerSeries_radical_coordinate_sandwich _ hrad
  exact ⟨powerSeries_thickening_equations_regular r c hc H e he hupper hlower,
    powerSeries_coordinateIdeal_power_quotient_finite _ e hlower,
    powerSeries_thickening_finite_free r c hr hc H e he hupper hlower⟩

def coordinateThickeningReductionFromRadical
    {r c : ℕ} (H : Fin c → AmbientRing r c) (hc : 0 < c)
    (hrad : (equationIdeal H).radical =
      Ideal.span (Set.range (MvPowerSeries.X (σ := Fin c) (R := ParameterRing r)))) :
    CompleteIntersection H →ₐ[ParameterRing r] ParameterRing r := by
  let : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
  exact powerSeriesThickeningReduction (equationIdeal H)
    (by rw [← hrad]; exact Ideal.le_radical)

theorem coordinateThickeningReductionFromRadical_kernel
    {r c : ℕ} (H : Fin c → AmbientRing r c) (hc : 0 < c)
    (hrad : (equationIdeal H).radical =
      Ideal.span (Set.range (MvPowerSeries.X (σ := Fin c) (R := ParameterRing r)))) :
    RingHom.ker (coordinateThickeningReductionFromRadical H hc hrad).toRingHom =
      nilradical (CompleteIntersection H) := by
  let : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
  obtain ⟨e, he, hupper, hlower⟩ := powerSeries_radical_coordinate_sandwich _ hrad
  exact powerSeriesThickeningReduction_kernel_nilradical _ e he hupper hlower

theorem formalThickening_relativeJacobian_socle
    {r c : ℕ} (H : Fin c → AmbientRing r c) (hr : 0 < r) (hc : 0 < c)
    (hrad : (equationIdeal H).radical =
      Ideal.span (Set.range (MvPowerSeries.X (σ := Fin c) (R := ParameterRing r)))) :
    let q := coordinateThickeningReductionFromRadical H hc hrad
    (∀ x : CompleteIntersection H,
      Annihilates (nilradical (CompleteIntersection H)) x ↔
        ∃ b : ParameterRing r, x = b • relativeJacobian H) ∧
    (∀ (τ : Fin r → CompleteIntersection H),
      Ideal.span (Set.range (fun i => q (τ i))) =
        IsLocalRing.maximalIdeal (ParameterRing r) →
      let J := Ideal.span (Set.range τ)
      let Q := CompleteIntersection H ⧸ J
      let m := (nilradical (CompleteIntersection H)).map (Ideal.Quotient.mk J)
      IsArtinianRing Q ∧ m.IsMaximal ∧
        m.annihilator = Ideal.span {Ideal.Quotient.mk J (relativeJacobian H)} ∧
        Ideal.Quotient.mk J (relativeJacobian H) ≠ 0) := by
  obtain ⟨hreg, hfinite, hfree⟩ := powerSeries_thickening_structure_from_radical r c hr hc H hrad
  let : Module.Free (ParameterRing r) (CompleteIntersection H) := hfree
  exact lemma31_complete r c H hr hc hreg hfinite Module.Flat.of_free
    (coordinateThickeningReductionFromRadical H hc hrad)
    (coordinateThickeningReductionFromRadical_kernel H hc hrad)

end LinearStudy
