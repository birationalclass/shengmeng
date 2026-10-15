module

public import Linear.PowerSeriesSocle
public import Linear.TraceElement

/-!
# Actual augmentation and trace element of the complete intersection

Construct the actual constant-coefficient K-algebra map on the power-series
quotient. Identify its kernel with the coordinate ideal and, for an Artinian
quotient, the nilradical. A normalized perfect pairing identifies its socle
generator with the dual reduction generator and its trace element with rank
times that generator. The derivative Jacobian comparison remains unproved.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace LinearStudy
variable {K : Type*} [Field K] {n : ℕ}

def powerSeriesConstantCoeffAlgHom : MvPowerSeries (Fin (n + 1)) K →ₐ[K] K :=
  { MvPowerSeries.constantCoeff with
    commutes' := fun k => by simp [MvPowerSeries.algebraMap_apply] }

theorem equationIdeal_le_constantCoeff_kernel
    (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K)
    (hzero : ∀ i, (H i).constantCoeff = 0) :
    Ideal.span (Set.range H) ≤ RingHom.ker
      (MvPowerSeries.constantCoeff (σ := Fin (n + 1)) (R := K)) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact hzero i

def powerSeriesQuotientAugmentation
    (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K)
    (hzero : ∀ i, (H i).constantCoeff = 0) :
    (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H)) →ₐ[K] K :=
  Ideal.Quotient.liftₐ _ powerSeriesConstantCoeffAlgHom
    (equationIdeal_le_constantCoeff_kernel H hzero)

@[simp] theorem powerSeriesQuotientAugmentation_mk
    (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K)
    (hzero : ∀ i, (H i).constantCoeff = 0)
    (r : MvPowerSeries (Fin (n + 1)) K) :
    powerSeriesQuotientAugmentation H hzero
      (Ideal.Quotient.mk (Ideal.span (Set.range H)) r) = r.constantCoeff := rfl

theorem powerSeriesQuotientAugmentation_kernel
    (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K)
    (hzero : ∀ i, (H i).constantCoeff = 0) :
    RingHom.ker (powerSeriesQuotientAugmentation H hzero).toRingHom =
      Ideal.span (Set.range (fun i =>
        Ideal.Quotient.mk (Ideal.span (Set.range H)) (MvPowerSeries.X i))) := by
  change RingHom.ker (Ideal.Quotient.lift (Ideal.span (Set.range H))
    (MvPowerSeries.constantCoeff (σ := Fin (n + 1)) (R := K)) _) = _
  rw [Ideal.ker_quotient_lift, powerSeries_constantCoeff_kernel,
    Ideal.map_span, ← Set.range_comp]
  rfl

theorem powerSeriesQuotientAugmentation_surjective
    (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K)
    (hzero : ∀ i, (H i).constantCoeff = 0) :
    Function.Surjective (powerSeriesQuotientAugmentation H hzero) := by
  intro k
  exact ⟨algebraMap K _ k, by simp⟩

theorem powerSeriesQuotientAugmentation_kernel_nilradical
    (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K)
    (hzero : ∀ i, (H i).constantCoeff = 0)
    [IsArtinianRing (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))] :
    RingHom.ker (powerSeriesQuotientAugmentation H hzero).toRingHom =
      nilradical (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H)) := by
  let A := MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H)
  let q := powerSeriesQuotientAugmentation H hzero
  let : Nontrivial A := q.toRingHom.domain_nontrivial
  let : IsLocalRing A := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (Ideal.span (Set.range H))) Ideal.Quotient.mk_surjective
  have hm := RingHom.ker_isMaximal_of_surjective q.toRingHom
    (powerSeriesQuotientAugmentation_surjective H hzero)
  rw [IsLocalRing.eq_maximalIdeal hm]
  rw [nilradical, ← IsArtinianRing.jacobson_eq_radical]
  exact (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A) bot_ne_top).symm

theorem powerSeries_socle_generator_dualGenerator
    (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K)
    (hzero : ∀ i, (H i).constantCoeff = 0)
    (delta : MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))
    (hd : delta ∈ (Ideal.span (Set.range (fun i =>
      Ideal.Quotient.mk (Ideal.span (Set.range H)) (MvPowerSeries.X i)))).annihilator)
    (p : PerfectMultiplicationPairing (B := K)
      (A := MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H)))
    (hp : p.functional delta = 1) :
    dualGenerator (powerSeriesQuotientAugmentation H hzero) p = delta := by
  have ha : Annihilates (RingHom.ker
      (powerSeriesQuotientAugmentation H hzero).toRingHom) delta := by
    rw [powerSeriesQuotientAugmentation_kernel]
    exact (annihilates_iff_mem_annihilator _ _).mpr hd
  have h := annihilator_eq_scalar_generator
    (powerSeriesQuotientAugmentation H hzero) p ha
  simpa [hp] using h.symm

theorem powerSeries_traceElement_eq_rank_socle
    (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K)
    (hzero : ∀ i, (H i).constantCoeff = 0)
    [IsArtinianRing (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))]
    [FiniteDimensional K (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))]
    (delta : MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))
    (hd : delta ∈ (Ideal.span (Set.range (fun i =>
      Ideal.Quotient.mk (Ideal.span (Set.range H)) (MvPowerSeries.X i)))).annihilator)
    (p : PerfectMultiplicationPairing (B := K)
      (A := MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H)))
    (hp : p.functional delta = 1) :
    traceElement p = Module.finrank K
      (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H)) • delta := by
  rw [traceElement_eq_rank_dualGenerator
    (powerSeriesQuotientAugmentation H hzero)
    (powerSeriesQuotientAugmentation_kernel_nilradical H hzero) p,
    powerSeries_socle_generator_dualGenerator H hzero delta hd p hp]

theorem powerSeries_completeIntersection_traceElement
    (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K)
    (hH : RingTheory.Sequence.IsRegular (MvPowerSeries (Fin (n + 1)) K) (List.ofFn H))
    (hzero : ∀ i, (H i).constantCoeff = 0)
    [IsArtinianRing (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))]
    [FiniteDimensional K (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))] :
    ∃ M : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPowerSeries (Fin (n + 1)) K),
      M.mulVec MvPowerSeries.X = H ∧
      ∃ p : PerfectMultiplicationPairing
        (B := K) (A := MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H)),
        p.functional (Ideal.Quotient.mk (Ideal.span (Set.range H)) M.det) = 1 ∧
        traceElement p = Module.finrank K
          (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H)) •
          Ideal.Quotient.mk (Ideal.span (Set.range H)) M.det := by
  obtain ⟨M, hM, p, hp⟩ := powerSeries_completeIntersection_perfectPairing H hH hzero
  refine ⟨M, hM, p, hp, powerSeries_traceElement_eq_rank_socle H hzero _ ?_ p hp⟩
  have ha := coefficientDeterminant_annihilates_quotient H MvPowerSeries.X M hM
  simpa [Ideal.map_span, ← Set.range_comp, Function.comp_def] using
    (annihilates_iff_mem_annihilator _ _).mp ha

end LinearStudy
