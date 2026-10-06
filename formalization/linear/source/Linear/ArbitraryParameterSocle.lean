module
public import Linear.ArbitraryParameterJacobian

/-! Complete proof of the exact Lemma31Goal, including socle generation for all permitted arbitrary parameter lifts. This local theorem does not prove the global Linearity Theorem. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace LinearStudy
theorem nonzero_socle_element_generates {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] [IsLocalRing A]
    (epsilon : A)
    (hgen : ∀ x : A, x ∈ (IsLocalRing.maximalIdeal A).annihilator →
      ∃ b : K, x = b • epsilon)
    (delta : A) (hd : delta ∈ (IsLocalRing.maximalIdeal A).annihilator) (hne : delta ≠ 0) :
    (IsLocalRing.maximalIdeal A).annihilator = Ideal.span {delta} := by
  obtain ⟨u, hu⟩ := hgen delta hd
  have hu0 : u ≠ 0 := by intro h; apply hne; simpa [h] using hu
  have he : epsilon = u⁻¹ • delta := by rw [hu, smul_smul, inv_mul_cancel₀ hu0, one_smul]
  apply le_antisymm
  · intro x hx
    obtain ⟨v, hv⟩ := hgen x hx
    apply Ideal.mem_span_singleton.mpr
    refine ⟨algebraMap K A (v * u⁻¹), ?_⟩
    rw [hv, he, smul_smul, Algebra.smul_def]
    exact mul_comm _ _
  · exact Ideal.span_le.mpr (by simpa using hd)

theorem finiteFlat_standard_closed_socle {r n : ℕ}
    (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) ℂ))
    (hH : RingTheory.Sequence.IsRegular
      (MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) ℂ)) (List.ofFn H))
    [Module.Finite (MvPowerSeries (Fin (r + 1)) ℂ)
      (MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) ℂ) ⧸ Ideal.span (Set.range H))]
    [Module.Flat (MvPowerSeries (Fin (r + 1)) ℂ)
      (MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) ℂ) ⧸ Ideal.span (Set.range H))] :
    let A := MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) ℂ) ⧸ Ideal.span (Set.range H)
    let J := Ideal.span (Set.range (fun i : Fin (r + 1) =>
      algebraMap (MvPowerSeries (Fin (r + 1)) ℂ) A (MvPowerSeries.X i)))
    ∀ (delta : A ⧸ J) [IsLocalRing (A ⧸ J)],
      delta ∈ (IsLocalRing.maximalIdeal (A ⧸ J)).annihilator → delta ≠ 0 →
      (IsLocalRing.maximalIdeal (A ⧸ J)).annihilator = Ideal.span {delta} := by
  dsimp only
  intro delta _ hd hne
  let B := MvPowerSeries (Fin (r + 1)) ℂ
  let R := MvPowerSeries (Fin (n + 1)) B
  let A := R ⧸ Ideal.span (Set.range H)
  let J := Ideal.span (Set.range (fun i : Fin (r + 1) => algebraMap B A (MvPowerSeries.X i)))
  let Hbar := fun i => parameterSpecialization (H i)
  let Q := MvPowerSeries (Fin (n + 1)) ℂ ⧸ Ideal.span (Set.range Hbar)
  have hreg := powerSeries_specialized_equations_regular H hH
  have hzero := powerSeries_specialized_equations_zeroConstant H hH
  have hproper : Ideal.span (Set.range Hbar) ≠ ⊤ := by
    intro ht
    apply hreg.top_ne_smul
    rw [ideal_ofFn, ht, Submodule.top_smul]
  let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hproper
  let : IsLocalRing Q := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (Ideal.span (Set.range Hbar))) Ideal.Quotient.mk_surjective
  let : IsArtinianRing Q := powerSeries_specialized_quotient_artinian H
  have hJ : (Ideal.span (Set.range (fun i : Fin (r + 1) =>
      (MvPowerSeries.C (MvPowerSeries.X i) : R)))).map (Ideal.Quotient.mk (Ideal.span (Set.range H))) = J := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  let E : (A ⧸ J) ≃+* Q := (Ideal.quotEquivOfEq hJ.symm).trans (powerSeriesClosedQuotientEquiv H)
  obtain ⟨M, hM, hdM, hsoc⟩ := powerSeries_coefficientDeterminant_scalar_socle Hbar hreg hzero
  have hgen : ∀ x : Q, x ∈ (IsLocalRing.maximalIdeal Q).annihilator →
      ∃ b : ℂ, x = b • Ideal.Quotient.mk (Ideal.span (Set.range Hbar)) M.det := by
    intro x hx
    apply hsoc x
    rwa [IsLocalRing.eq_maximalIdeal (powerSeries_quotient_coordinateIdeal_isMaximal Hbar hzero)]
  have hnon : E delta ≠ 0 := by intro hz; apply hne; exact E.injective (by simpa using hz)
  have heq := nonzero_socle_element_generates _ hgen (E delta)
    (ringEquiv_socle_forward E delta hd) hnon
  apply le_antisymm
  · intro x hx
    have hxE := ringEquiv_socle_forward E x hx
    rw [heq] at hxE
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hxE
    refine (Ideal.mem_span_singleton (x := x) (y := delta)).mpr ⟨E.symm a, E.injective ?_⟩
    calc
      E x = E delta * a := ha
      _ = E delta * E (E.symm a) := by rw [E.apply_symm_apply]
      _ = E (delta * E.symm a) := (E.map_mul _ _).symm
  · exact Ideal.span_le.mpr (by simpa using hd)

theorem annihilates_quotient_image {A : Type*} [CommRing A] (I J : Ideal A)
    (delta : A) (hd : Annihilates I delta) :
    Ideal.Quotient.mk J delta ∈ (I.map (Ideal.Quotient.mk J)).annihilator := by
  apply Submodule.mem_annihilator.mpr
  intro n hn
  obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective).mp hn
  change Ideal.Quotient.mk J delta * Ideal.Quotient.mk J a = 0
  rw [← map_mul, mul_comm delta, hd a ha, map_zero]

theorem lemma31_arbitrary_parameter_socle_generation {r c : ℕ}
    (H : Fin c → AmbientRing r c) (hr : 0 < r) (hc : 0 < c)
    (hH : RingTheory.Sequence.IsRegular (AmbientRing r c) (List.ofFn H))
    [Module.Finite (ParameterRing r) (CompleteIntersection H)]
    [Module.Flat (ParameterRing r) (CompleteIntersection H)]
    (q : CompleteIntersection H →ₐ[ParameterRing r] ParameterRing r)
    (hq : RingHom.ker q.toRingHom = nilradical (CompleteIntersection H))
    (tau : Fin r → CompleteIntersection H)
    (htau : Ideal.span (Set.range (fun i => q (tau i))) =
      IsLocalRing.maximalIdeal (ParameterRing r)) :
    let J := Ideal.span (Set.range tau)
    ((nilradical (CompleteIntersection H)).map (Ideal.Quotient.mk J)).annihilator =
      Ideal.span {Ideal.Quotient.mk J (relativeJacobian H)} := by
  have hnon := lemma31_arbitrary_parameter_jacobian_nonzero H hr hc hH q hq tau htau
  have hd : Annihilates (nilradical (CompleteIntersection H)) (relativeJacobian H) :=
    (lemma31_annihilator_conclusion H hr hc hH q hq _).mpr ⟨1, by simp⟩
  obtain ⟨H', E, q', hEX, hH', hfinite, hfree, hq'⟩ :=
    completeIntersection_lifted_parameter_presentation H hr hc hH q hq tau htau
  dsimp only [CompleteIntersection, equationIdeal, AmbientRing, ParameterRing] at *
  let B := MvPowerSeries (Fin r) ℂ
  let R := MvPowerSeries (Fin c) B
  let A := R ⧸ Ideal.span (Set.range H)
  let D := R ⧸ Ideal.span (Set.range H')
  change A →ₐ[B] B at q
  change D →ₐ[B] B at q'
  change D ≃+* A at E
  change Fin r → A at tau
  let J : Ideal A := Ideal.span (Set.range tau)
  let J' := Ideal.span (Set.range (fun i : Fin r => algebraMap B D (MvPowerSeries.X i)))
  have hJE : J = J'.map E.toRingHom := by
    rw [Ideal.map_span, ← Set.range_comp]
    change Ideal.span (Set.range tau) =
      Ideal.span (Set.range (fun i : Fin r => E (algebraMap B D (MvPowerSeries.X i))))
    rw [show (fun i : Fin r => E (algebraMap B D (MvPowerSeries.X i))) = tau from funext hEX]
  let EQ := Ideal.quotientEquiv J' J E hJE
  let : Module.Finite B D := hfinite
  let : Module.Free B D := hfree
  let : Module.Flat B D := Module.Flat.of_free
  let : IsNoetherianRing A := isNoetherianRing_of_surjective (AmbientRing r c) A
    (Ideal.Quotient.mk (equationIdeal H)) Ideal.Quotient.mk_surjective
  let : IsNoetherianRing D := isNoetherianRing_of_surjective (AmbientRing r c) D
    (Ideal.Quotient.mk (equationIdeal H')) Ideal.Quotient.mk_surjective
  have hJq : J.map q.toRingHom = IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_span, ← Set.range_comp]
    exact htau
  have hJq' : J'.map q'.toRingHom = IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_span, ← Set.range_comp]
    change Ideal.span (Set.range (fun i : Fin r => q' (algebraMap B D (MvPowerSeries.X i)))) = _
    rw [show (fun i : Fin r => q' (algebraMap B D (MvPowerSeries.X i))) =
      (fun i : Fin r => (MvPowerSeries.X i : B)) from funext (fun i => q'.commutes _)]
    let : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    exact powerSeries_coordinateIdeal_eq_maximalIdeal
  let : IsLocalRing (A ⧸ J) := (parameterQuotient_local_artinian q hq J hJq).2
  let : IsLocalRing (D ⧸ J') := (parameterQuotient_local_artinian q' hq' J' hJq').2
  let delta : A ⧸ J := Ideal.Quotient.mk J (relativeJacobian H)
  have hM : ((nilradical A).map (Ideal.Quotient.mk J)).IsMaximal :=
    parameterQuotient_nilradical_image_isMaximal q hq J hJq
  have hm : (nilradical A).map (Ideal.Quotient.mk J) = IsLocalRing.maximalIdeal (A ⧸ J) := by
    exact IsLocalRing.eq_maximalIdeal (R := A ⧸ J)
      (I := (nilradical A).map (Ideal.Quotient.mk J)) hM
  have hdQ : delta ∈ (IsLocalRing.maximalIdeal (A ⧸ J)).annihilator := by
    rw [← hm]
    exact annihilates_quotient_image _ J _ hd
  have hdelta : EQ.symm delta ≠ 0 := by
    intro h
    apply hnon
    have hh := congrArg EQ h
    simpa only [EQ.apply_symm_apply, map_zero] using hh
  have hdD := ringEquiv_socle_forward (C := A ⧸ J) (D := D ⧸ J') EQ.symm delta hdQ
  have hgen : (IsLocalRing.maximalIdeal (D ⧸ J')).annihilator = Ideal.span {EQ.symm delta} := by
    cases r with
    | zero => exact False.elim (Nat.not_lt_zero _ hr)
    | succ r =>
      cases c with
      | zero => exact False.elim (Nat.not_lt_zero _ hc)
      | succ n => exact finiteFlat_standard_closed_socle H' hH' (EQ.symm delta) hdD hdelta
  change ((nilradical A).map (Ideal.Quotient.mk J)).annihilator = Ideal.span {delta}
  rw [hm]
  apply le_antisymm
  · intro x hx
    have hx' := ringEquiv_socle_forward (C := A ⧸ J) (D := D ⧸ J') EQ.symm x hx
    rw [hgen] at hx'
    obtain ⟨a, ha⟩ := (Ideal.mem_span_singleton (α := D ⧸ J')
      (x := EQ.symm x) (y := EQ.symm delta)).mp hx'
    refine (Ideal.mem_span_singleton (x := x) (y := delta)).mpr ⟨EQ a, EQ.symm.injective ?_⟩
    calc
      EQ.symm x = EQ.symm delta * a := ha
      _ = EQ.symm delta * EQ.symm (EQ a) := by rw [EQ.symm_apply_apply]
      _ = EQ.symm (delta * EQ a) := (EQ.symm.map_mul _ _).symm
  · exact Ideal.span_le.mpr (by simpa using hdQ)

theorem lemma31_complete (r c : ℕ) : Lemma31Goal r c := by
  intro H hr hc hH hfinite hflat q hq
  let : Module.Finite (ParameterRing r) (CompleteIntersection H) := hfinite
  let : Module.Flat (ParameterRing r) (CompleteIntersection H) := hflat
  refine ⟨lemma31_annihilator_conclusion H hr hc hH q hq, ?_⟩
  intro tau htau
  obtain ⟨hArt, hMax⟩ := completeIntersection_parameterQuotient_artinian H q hq tau htau
  exact ⟨hArt, hMax, lemma31_arbitrary_parameter_socle_generation H hr hc hH q hq tau htau,
    lemma31_arbitrary_parameter_jacobian_nonzero H hr hc hH q hq tau htau⟩
end LinearStudy
