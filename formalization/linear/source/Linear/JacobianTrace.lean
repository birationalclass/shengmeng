module
public import Linear.ArtinianDiagonal
public import Linear.DiagonalTrace

/-!
# Actual multivariable Jacobian is a trace multiple and annihilates the nilradical

Apply the constructed diagonal difference matrix and the actual tensor/trace
equivalence. Its Jacobian image is a multiple of the trace element. For an
Artinian finite-dimensional regular equation quotient, construct the pairing
and deduce annihilation of the nilradical by the actual derivative Jacobian.
The multiplying coefficient is not yet proved a unit, so Jacobian
nonvanishing and generation of the socle are NOT conclusions here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000
namespace LinearStudy
variable {K : Type*} [Field K] {n : ℕ}

def powerSeriesJacobianClass
    (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K) :
    MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H) :=
  Ideal.Quotient.mk (Ideal.span (Set.range H))
    (Matrix.det (fun i j => MvPowerSeries.pderiv j (H i)))

theorem powerSeriesQuotient_jacobian_trace_multiple
    (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K)
    (hzero : ∀ i, (H i).constantCoeff = 0)
    [IsArtinianRing (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))]
    [FiniteDimensional K (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))]
    (p : PerfectMultiplicationPairing (B := K)
      (A := MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))) :
    ∃ c, powerSeriesJacobianClass H = c * traceElement p := by
  let Q := MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H)
  let q := Ideal.Quotient.mk (Ideal.span (Set.range H))
  obtain ⟨M, hM, hd⟩ := powerSeriesQuotient_diagonal_jacobian H hzero
  have hJ : powerSeriesJacobianClass H =
      Matrix.det (fun i j => q (MvPowerSeries.pderiv j (H i))) := by
    exact q.map_det _
  refine ⟨pairingTensorEndEquiv p M.det 1, ?_⟩
  rw [hJ, ← hd]
  exact diagonal_annihilator_multiplication_eq_trace_multiple p M.det hM

theorem powerSeriesQuotient_jacobian_annihilates_nilradical
    (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K)
    (hH : RingTheory.Sequence.IsRegular (MvPowerSeries (Fin (n + 1)) K) (List.ofFn H))
    (hzero : ∀ i, (H i).constantCoeff = 0)
    [IsArtinianRing (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))]
    [FiniteDimensional K (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))] :
    Annihilates (nilradical (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H)))
      (powerSeriesJacobianClass H) := by
  obtain ⟨N, hN, p, hp⟩ := powerSeries_completeIntersection_perfectPairing H hH hzero
  obtain ⟨c, hc⟩ := powerSeriesQuotient_jacobian_trace_multiple H hzero p
  have ht := traceElement_annihilates_kernel (powerSeriesQuotientAugmentation H hzero)
    (powerSeriesQuotientAugmentation_kernel_nilradical H hzero) p
  rw [powerSeriesQuotientAugmentation_kernel_nilradical H hzero] at ht
  rw [hc]
  intro a ha
  calc
    a * (c * traceElement p) = c * (a * traceElement p) := by ring
    _ = 0 := by rw [ht a ha, mul_zero]

end LinearStudy
