module
public import Linear.RelativeJacobianTrace
public import Linear.JacobianSpecialization
/-!
# Relative Jacobian generation after centering the normal coordinates

For the original finite flat regular equations over a characteristic-zero
power-series base, derive the actual derivative Jacobian's scalar generation
of the nilradical annihilator. The reduction map has nilradical kernel and
sends the actual normal coordinate classes to zero. Pairing and primitivity
are constructed, not assumed. This proves the post-centering portion of the
manuscript: the coordinate translation and arbitrary parameter-lift results
are still separate unfinished obligations.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace LinearStudy
variable {K : Type*} [Field K] [CharZero K] {r n : ℕ}

theorem finiteFlat_centered_jacobian_annihilator
    (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) K))
    (hH : RingTheory.Sequence.IsRegular
      (MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) K)) (List.ofFn H))
    [Module.Finite (MvPowerSeries (Fin (r + 1)) K)
      (MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) K) ⧸ Ideal.span (Set.range H))]
    [Module.Flat (MvPowerSeries (Fin (r + 1)) K)
      (MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) K) ⧸ Ideal.span (Set.range H))]
    (a : (MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) K) ⧸
      Ideal.span (Set.range H)) →ₐ[MvPowerSeries (Fin (r + 1)) K] MvPowerSeries (Fin (r + 1)) K)
    (ha : RingHom.ker a.toRingHom = nilradical
      (MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) K) ⧸ Ideal.span (Set.range H)))
    (hz : ∀ i, a (Ideal.Quotient.mk (Ideal.span (Set.range H)) (MvPowerSeries.X i)) = 0)
    (x : MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) K) ⧸ Ideal.span (Set.range H)) :
    Annihilates (nilradical
      (MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) K) ⧸ Ideal.span (Set.range H))) x ↔
      ∃ u : MvPowerSeries (Fin (r + 1)) K,
        x = u • Ideal.Quotient.mk (Ideal.span (Set.range H))
          (Matrix.det (fun i j => MvPowerSeries.pderiv j (H i))) := by
  let B := MvPowerSeries (Fin (r + 1)) K
  let A := MvPowerSeries (Fin (n + 1)) B ⧸ Ideal.span (Set.range H)
  let : Module.Free B A := Module.free_of_flat_of_isLocalRing
  obtain ⟨p⟩ := finiteFlat_powerSeries_relative_perfectPairing H hH
  have hnil : ∀ i, IsNilpotent (Ideal.Quotient.mk (Ideal.span (Set.range H))
      (MvPowerSeries.X i)) := by
    intro i
    apply mem_nilradical.mp
    rw [← ha]
    exact hz i
  have hd := relativePowerSeriesQuotient_jacobian_annihilates_nilradical H hnil a ha p
  have hd' : Annihilates (RingHom.ker a.toRingHom)
      (Ideal.Quotient.mk (Ideal.span (Set.range H))
        (Matrix.det (fun i j => MvPowerSeries.pderiv j (H i)))) := by
    rwa [ha]
  have hx := primitive_annihilator_generates a p _ hd'
    (finiteFlat_jacobian_primitive H hH) x
  rwa [ha] at hx
end LinearStudy
