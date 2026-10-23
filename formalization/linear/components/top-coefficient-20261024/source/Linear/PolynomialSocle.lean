module
public import Linear.PowerSeriesSocle

/-!
# PolynomialSocle

For original regular power-series equations with Artinian quotient, a unit change of equations preserves nonvanishing of any resulting coefficient determinant. Regularity of the changed equations is not assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace LinearStudy
variable {K : Type*} [Field K] {n : ℕ}

theorem powerSeries_unit_changed_coefficientDeterminant_ne_zero
    (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K)
    (hH : RingTheory.Sequence.IsRegular (MvPowerSeries (Fin (n + 1)) K) (List.ofFn H))
    (hzero : ∀ i, (H i).constantCoeff = 0)
    [IsArtinianRing (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))]
    (U N : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPowerSeries (Fin (n + 1)) K))
    (hU : IsUnit U) (he : U.mulVec H = N.mulVec MvPowerSeries.X) :
    Ideal.Quotient.mk (Ideal.span (Set.range H)) N.det ≠ 0 := by
  classical
  let R := MvPowerSeries (Fin (n + 1)) K
  let I := Ideal.span (Set.range H)
  have hI : I ≠ ⊤ := by
    intro ht
    change Ideal.span (Set.range H) = ⊤ at ht
    apply hH.top_ne_smul
    rw [ideal_ofFn, ht]
    simp
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  let : IsLocalRing (R ⧸ I) := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  obtain ⟨u, rfl⟩ := hU
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) R := (↑u⁻¹ : Matrix _ _ R) * N
  have hM : M.mulVec MvPowerSeries.X = H := by
    rw [show M = (↑u⁻¹ : Matrix _ _ R) * N from rfl,
      ← Matrix.mulVec_mulVec, ← he, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hx := powerSeries_variables_regular (R := K) (n + 1)
  have hm := IsLocalRing.eq_maximalIdeal
    (powerSeries_quotient_coordinateIdeal_isMaximal H hzero)
  have hm' : (Ideal.span (Set.range (MvPowerSeries.X (σ := Fin (n + 1)) (R := K)))).map
      (Ideal.Quotient.mk I) = IsLocalRing.maximalIdeal (R ⧸ I) := by
    simpa [Ideal.map_span, ← Set.range_comp, Function.comp_def] using hm
  have hd := coefficientDeterminant_ne_zero_of_local_artinian H MvPowerSeries.X
    hH hx M hM hm'
  intro hz
  apply hd
  simp only [M, Matrix.det_mul, map_mul, hz, mul_zero]

end LinearStudy
