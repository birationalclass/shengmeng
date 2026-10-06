module

public import Linear.KoszulSocleDeterminant
public import Linear.PowerSeriesRegular
public import Linear.PowerSeriesCoefficients

/-!
# The actual power-series complete-intersection socle

For H a regular sequence in K[[X_0,...,X_n]] with zero constant terms,
assume its actual quotient is Artinian. Construct H = M X and prove
that det M is nonzero and generates the socle, also as a K-vector space.
Finite-dimensionality is explicit only for the perfect-pairing corollary.
The actual derivative Jacobian has not yet been identified with this
coefficient determinant or the algebraic trace element.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open RingTheory.Sequence
namespace LinearStudy
variable {K : Type*} [Field K] {n : ℕ}

theorem powerSeries_socle_mul_constant (I : Ideal (MvPowerSeries (Fin (n + 1)) K))
    (delta : MvPowerSeries (Fin (n + 1)) K ⧸ I)
    (hd : delta ∈ (Ideal.span (Set.range (fun i =>
      Ideal.Quotient.mk I (MvPowerSeries.X i)))).annihilator)
    (r : MvPowerSeries (Fin (n + 1)) K) :
    Ideal.Quotient.mk I r * delta = r.constantCoeff • delta := by
  let q := Ideal.Quotient.mk I
  have hr : r - MvPowerSeries.C r.constantCoeff ∈
      RingHom.ker (MvPowerSeries.constantCoeff (σ := Fin (n + 1)) (R := K)) := by
    change (r - MvPowerSeries.C r.constantCoeff).constantCoeff = 0
    simp
  rw [powerSeries_constantCoeff_kernel] at hr
  have hm := Ideal.mem_map_of_mem q hr
  rw [Ideal.map_span, ← Set.range_comp] at hm
  have hz := Submodule.mem_annihilator.mp hd _ hm
  change delta * q (r - MvPowerSeries.C r.constantCoeff) = 0 at hz
  rw [map_sub, mul_sub, sub_eq_zero] at hz
  rw [mul_comm delta] at hz
  have hs : q (MvPowerSeries.C r.constantCoeff) * delta = r.constantCoeff • delta := by
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective delta
    change q (MvPowerSeries.C r.constantCoeff * d) = q (r.constantCoeff • d)
    rw [MvPowerSeries.smul_eq_C_mul]
  exact hz.trans (by rw [mul_comm, hs])

theorem powerSeries_coefficientDeterminant_socle
    (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K)
    (hH : IsRegular (MvPowerSeries (Fin (n + 1)) K) (List.ofFn H))
    (hzero : ∀ i, (H i).constantCoeff = 0)
    [IsArtinianRing (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))] :
    ∃ M : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPowerSeries (Fin (n + 1)) K),
      M.mulVec MvPowerSeries.X = H ∧
      Ideal.Quotient.mk (Ideal.span (Set.range H)) M.det ≠ 0 ∧
      (Ideal.span (Set.range (fun i =>
        Ideal.Quotient.mk (Ideal.span (Set.range H)) (MvPowerSeries.X i)))).annihilator =
        Ideal.span {Ideal.Quotient.mk (Ideal.span (Set.range H)) M.det} := by
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
  obtain ⟨M, hM⟩ := powerSeries_equation_coefficient_matrix H hzero
  have hx := powerSeries_variables_regular (R := K) (n + 1)
  have hm := powerSeries_quotient_coordinateIdeal_isMaximal H hzero
  have he := IsLocalRing.eq_maximalIdeal hm
  have he' : (Ideal.span (Set.range (MvPowerSeries.X (σ := Fin (n + 1)) (R := K)))).map
      (Ideal.Quotient.mk I) = IsLocalRing.maximalIdeal (R ⧸ I) := by
    simpa [Ideal.map_span, ← Set.range_comp, Function.comp_def] using he
  refine ⟨M, hM, coefficientDeterminant_ne_zero_of_local_artinian H MvPowerSeries.X
    hH hx M hM he', ?_⟩
  have hgen := coordinate_annihilator_eq_coefficientDeterminant H MvPowerSeries.X hH hx M hM
  simpa [Ideal.map_span, ← Set.range_comp, Function.comp_def] using hgen

theorem powerSeries_coefficientDeterminant_scalar_socle
    (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K)
    (hH : IsRegular (MvPowerSeries (Fin (n + 1)) K) (List.ofFn H))
    (hzero : ∀ i, (H i).constantCoeff = 0)
    [IsArtinianRing (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))] :
    ∃ M : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPowerSeries (Fin (n + 1)) K),
      M.mulVec MvPowerSeries.X = H ∧
      Ideal.Quotient.mk (Ideal.span (Set.range H)) M.det ≠ 0 ∧
      ∀ a : MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H),
        a ∈ (Ideal.span (Set.range (fun i =>
          Ideal.Quotient.mk (Ideal.span (Set.range H)) (MvPowerSeries.X i)))).annihilator →
        ∃ b : K, a = b • Ideal.Quotient.mk (Ideal.span (Set.range H)) M.det := by
  obtain ⟨M, hM, hd, hgen⟩ := powerSeries_coefficientDeterminant_socle H hH hzero
  refine ⟨M, hM, hd, ?_⟩
  intro a ha
  rw [hgen] at ha
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective b
  have hm : Ideal.Quotient.mk (Ideal.span (Set.range H)) M.det ∈
      (Ideal.span (Set.range (fun i =>
        Ideal.Quotient.mk (Ideal.span (Set.range H)) (MvPowerSeries.X i)))).annihilator := by
    rw [hgen]
    exact Ideal.subset_span (Set.mem_singleton _)
  refine ⟨r.constantCoeff, ?_⟩
  rw [hb, ← hr, mul_comm]
  exact powerSeries_socle_mul_constant _ _ hm r

theorem powerSeries_completeIntersection_perfectPairing
    (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K)
    (hH : IsRegular (MvPowerSeries (Fin (n + 1)) K) (List.ofFn H))
    (hzero : ∀ i, (H i).constantCoeff = 0)
    [IsArtinianRing (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))]
    [FiniteDimensional K (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))] :
    ∃ M : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPowerSeries (Fin (n + 1)) K),
      M.mulVec MvPowerSeries.X = H ∧
      ∃ p : PerfectMultiplicationPairing
        (B := K) (A := MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H)),
        p.functional (Ideal.Quotient.mk (Ideal.span (Set.range H)) M.det) = 1 := by
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
  obtain ⟨M, hM, hd, hgen⟩ := powerSeries_coefficientDeterminant_scalar_socle H hH hzero
  have he := IsLocalRing.eq_maximalIdeal
    (powerSeries_quotient_coordinateIdeal_isMaximal H hzero)
  refine ⟨M, hM, exists_perfectPairing_of_scalar_socle _ hd ?_⟩
  intro a ha
  rw [← he] at ha
  exact hgen a ha

end LinearStudy
