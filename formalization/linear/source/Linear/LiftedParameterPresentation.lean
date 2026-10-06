module
public import Linear.LiftedParameterMaps
public import Linear.LiftedParametersRegular
public import Linear.RegularGeneratorsFree
public import Mathlib.RingTheory.Finiteness.NilpotentKer

/-! Construct a new regular equation quotient and compatible reduction for arbitrary parameter lifts. Its finiteness and freeness are proved from the original flat regular setting, not assumed. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace LinearStudy
def ringEquationChangeQuotientEquiv {R : Type*} [CommRing R] {ι : Type*}
    (e : R ≃+* R) (H : ι → R) :
    (R ⧸ Ideal.span (Set.range H)) ≃+*
      (R ⧸ Ideal.span (Set.range (fun i => e (H i)))) :=
  Ideal.quotientEquiv _ _ e (by
    rw [Ideal.map_span]
    congr 1
    ext x
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨H i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩)

theorem ringEquationChangeQuotientEquiv_mk {R : Type*} [CommRing R] {ι : Type*}
    (e : R ≃+* R) (H : ι → R) (x : R) :
    ringEquationChangeQuotientEquiv e H (Ideal.Quotient.mk (Ideal.span (Set.range H)) x) =
      Ideal.Quotient.mk (Ideal.span (Set.range (fun i => e (H i)))) (e x) := rfl

theorem regularSequence_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (H : List R) :
    RingTheory.Sequence.IsRegular R H ↔ RingTheory.Sequence.IsRegular S (H.map e) := by
  apply e.toAddEquiv.isRegular_congr
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro r _ x
  exact e.map_mul r x

theorem completeIntersection_lifted_parameter_presentation
    {r c : ℕ} (H : Fin c → AmbientRing r c) (hr : 0 < r) (hc : 0 < c)
    (hH : RingTheory.Sequence.IsRegular (AmbientRing r c) (List.ofFn H))
    [Module.Flat (ParameterRing r) (CompleteIntersection H)]
    (q : CompleteIntersection H →ₐ[ParameterRing r] ParameterRing r)
    (hq : RingHom.ker q.toRingHom = nilradical (CompleteIntersection H))
    (tau : Fin r → CompleteIntersection H)
    (htau : Ideal.span (Set.range (fun i => q (tau i))) =
      IsLocalRing.maximalIdeal (ParameterRing r)) :
    ∃ H' : Fin c → AmbientRing r c,
      ∃ E : CompleteIntersection H' ≃+* CompleteIntersection H,
      ∃ q' : CompleteIntersection H' →ₐ[ParameterRing r] ParameterRing r,
        (∀ i, E (algebraMap (ParameterRing r) (CompleteIntersection H') (MvPowerSeries.X i)) = tau i) ∧
        RingTheory.Sequence.IsRegular (AmbientRing r c) (List.ofFn H') ∧
        Module.Finite (ParameterRing r) (CompleteIntersection H') ∧
        Module.Free (ParameterRing r) (CompleteIntersection H') ∧
        RingHom.ker q'.toRingHom = nilradical (CompleteIntersection H') := by
  have hreg := completeIntersection_parameter_lifts_regular H hr hH q hq tau htau
  obtain ⟨e, he, heC⟩ := completeIntersection_lifted_coordinate_equiv_exists H hc q tau htau
  dsimp only [CompleteIntersection, equationIdeal, AmbientRing, ParameterRing] at *
  let : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  let B := ParameterRing r
  let R := AmbientRing r c
  let I := Ideal.span (Set.range H)
  let H' := fun i => e.symm (H i)
  let I' := Ideal.span (Set.range H')
  let E : (R ⧸ I') ≃+* (R ⧸ I) := (ringEquationChangeQuotientEquiv e.symm H).symm
  have hmk (z : R) : E (Ideal.Quotient.mk I' z) = Ideal.Quotient.mk I (e z) := by
    apply (ringEquationChangeQuotientEquiv e.symm H).injective
    rw [RingEquiv.apply_symm_apply, ringEquationChangeQuotientEquiv_mk,
      RingEquiv.symm_apply_apply]
  have hEX (i : Fin r) : E (algebraMap B (R ⧸ I') (MvPowerSeries.X i)) = tau i := by
    change E (Ideal.Quotient.mk I' (MvPowerSeries.C (MvPowerSeries.X i))) = _
    rw [hmk]
    exact he i
  let f : B →+* B := q.toRingHom.comp (E.toRingHom.comp (algebraMap B (R ⧸ I')))
  have hfX : Ideal.span (Set.range (fun i => f (MvPowerSeries.X i))) =
      IsLocalRing.maximalIdeal B := by
    have hx : (fun i => f (MvPowerSeries.X i)) = (fun i => q (tau i)) := by
      funext i
      change q (E (algebraMap B (R ⧸ I') (MvPowerSeries.X i))) = _
      rw [hEX]
    rw [hx]
    exact htau
  have hfC (k : ℂ) : f (MvPowerSeries.C k) = MvPowerSeries.C k := by
    change q (E (Ideal.Quotient.mk I' (MvPowerSeries.C (MvPowerSeries.C k)))) = _
    rw [hmk, heC]
    exact q.commutes _
  let alpha := RingEquiv.ofBijective f
    (powerSeries_ringEnd_bijective_of_parameter_images f hfX hfC)
  let qR : (R ⧸ I') →+* B := alpha.symm.toRingHom.comp (q.toRingHom.comp E.toRingHom)
  let q' : (R ⧸ I') →ₐ[B] B := { qR with
    commutes' := fun b => by
      change alpha.symm (f b) = b
      exact alpha.symm_apply_apply b }
  have hq' : RingHom.ker q'.toRingHom = nilradical (R ⧸ I') := by
    ext x
    rw [RingHom.mem_ker, mem_nilradical]
    change alpha.symm (q (E x)) = 0 ↔ IsNilpotent x
    rw [map_eq_zero_iff _ alpha.symm.injective]
    have h : q (E x) = 0 ↔ IsNilpotent (E x) := by
      rw [← mem_nilradical, ← hq, RingHom.mem_ker]
      rfl
    rw [h]
    constructor
    · intro hx
      simpa only [E.symm_apply_apply] using hx.map E.symm
    · intro hx
      exact hx.map E
  let : IsNoetherianRing (R ⧸ I') := isNoetherianRing_of_surjective R _
    (Ideal.Quotient.mk I') Ideal.Quotient.mk_surjective
  let : Module.Finite B (R ⧸ I') := Module.finite_of_surjective_of_ker_le_nilradical q'
    (fun b => ⟨algebraMap B (R ⧸ I') b, q'.commutes b⟩)
    (by change RingHom.ker q'.toRingHom ≤ _; exact hq'.le)
    (IsNoetherian.noetherian _)
  have hnew : RingTheory.Sequence.IsRegular (R ⧸ I')
      ((List.ofFn (fun i : Fin r => MvPowerSeries.X i)).map (algebraMap B (R ⧸ I'))) := by
    have h := (regularSequence_ringEquiv E
      ((List.ofFn (fun i : Fin r => MvPowerSeries.X i)).map (algebraMap B (R ⧸ I')))).mpr
    apply h
    rw [List.map_map, List.map_ofFn]
    change RingTheory.Sequence.IsRegular (R ⧸ I) (List.ofFn (fun i => E (algebraMap B (R ⧸ I') (MvPowerSeries.X i))))
    simpa only [hEX] using hreg
  have hgen : Ideal.ofList (List.ofFn (fun i : Fin r => (MvPowerSeries.X i : B))) =
      IsLocalRing.maximalIdeal B := by
    rw [show Ideal.ofList (List.ofFn (fun i : Fin r => (MvPowerSeries.X i : B))) =
      Ideal.span (Set.range (fun i : Fin r => (MvPowerSeries.X i : B))) by
      simp [Ideal.ofList, List.mem_ofFn, Set.range]]
    exact powerSeries_coordinateIdeal_eq_maximalIdeal
  let : Module.Free B (R ⧸ I') :=
    free_of_regular_maximal_algebraMap _ hnew.toIsWeaklyRegular hgen
  have hH' : RingTheory.Sequence.IsRegular R (List.ofFn H') := by
    rw [show List.ofFn H' = (List.ofFn H).map e.symm by rw [List.map_ofFn]; rfl]
    exact (regularSequence_ringEquiv e.symm (List.ofFn H)).mp hH
  exact ⟨H', E, q', hEX, hH', inferInstance, inferInstance, hq'⟩
end LinearStudy
