module
public import Linear.LiftedParameterPresentation
public import Linear.RelativeJacobian
public import Linear.ParameterPairingChange

/-! The actual relative Jacobian survives every arbitrary parameter ideal. New parameter presentation, finite freeness and perfect pairing are constructed in the proof. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace LinearStudy
theorem annihilates_nilradical_ringEquiv {A D : Type*} [CommRing A] [CommRing D]
    (e : D ≃+* A) (x : D) : Annihilates (nilradical D) x ↔
      Annihilates (nilradical A) (e x) := by
  constructor
  · intro h n hn
    apply e.symm.injective
    rw [map_mul, map_zero, e.symm_apply_apply]
    apply h
    exact mem_nilradical.mpr ((mem_nilradical.mp hn).map e.symm)
  · intro h n hn
    apply e.injective
    rw [map_mul, map_zero]
    apply h
    exact mem_nilradical.mpr ((mem_nilradical.mp hn).map e)

theorem annihilator_scalar_generation_ringEquiv
    {B A D : Type*} [CommRing B] [CommRing A] [CommRing D]
    [Algebra B A] [Algebra B D]
    (e : D ≃+* A) (q' : D →ₐ[B] B)
    (hq' : RingHom.ker q'.toRingHom = nilradical D)
    (delta : A) (hd : Annihilates (nilradical A) delta)
    (hgen : ∀ x : A, Annihilates (nilradical A) x → ∃ b : B, x = b • delta)
    (x : D) (hx : Annihilates (nilradical D) x) :
    ∃ b : B, x = b • e.symm delta := by
  have hxA := (annihilates_nilradical_ringEquiv e x).mp hx
  have hdD := (annihilates_nilradical_ringEquiv e (e.symm delta)).mpr
    (by rw [e.apply_symm_apply]; exact hd)
  obtain ⟨b, hb⟩ := hgen (e x) hxA
  refine ⟨q' (e.symm (algebraMap B A b)), ?_⟩
  have hz : ∀ a : D, q' a = 0 ↔ a ∈ nilradical D := by
    intro a
    change a ∈ RingHom.ker q'.toRingHom ↔ _
    rw [hq']
  calc
    x = e.symm (b • delta) := by rw [← hb, e.symm_apply_apply]
    _ = e.symm (algebraMap B A b) * e.symm delta := by rw [Algebra.smul_def, map_mul]
    _ = algebraMap B D (q' (e.symm (algebraMap B A b))) * e.symm delta :=
      multiplication_factors_through_reduction q' hz hdD _
    _ = _ := (Algebra.smul_def _ _).symm

theorem completeIntersection_parameter_pairing {r c : ℕ}
    (H : Fin c → AmbientRing r c) (hr : 0 < r) (hc : 0 < c)
    (hH : RingTheory.Sequence.IsRegular (AmbientRing r c) (List.ofFn H))
    [Module.Finite (ParameterRing r) (CompleteIntersection H)]
    [Module.Flat (ParameterRing r) (CompleteIntersection H)] :
    Nonempty (PerfectMultiplicationPairing (B := ParameterRing r) (A := CompleteIntersection H)) := by
  dsimp only [CompleteIntersection, equationIdeal, AmbientRing, ParameterRing] at *
  cases r with
  | zero => exact False.elim (Nat.not_lt_zero _ hr)
  | succ r =>
    cases c with
    | zero => exact False.elim (Nat.not_lt_zero _ hc)
    | succ n => exact finiteFlat_powerSeries_relative_perfectPairing H hH

theorem lemma31_arbitrary_parameter_jacobian_nonzero {r c : ℕ}
    (H : Fin c → AmbientRing r c) (hr : 0 < r) (hc : 0 < c)
    (hH : RingTheory.Sequence.IsRegular (AmbientRing r c) (List.ofFn H))
    [Module.Finite (ParameterRing r) (CompleteIntersection H)]
    [Module.Flat (ParameterRing r) (CompleteIntersection H)]
    (q : CompleteIntersection H →ₐ[ParameterRing r] ParameterRing r)
    (hq : RingHom.ker q.toRingHom = nilradical (CompleteIntersection H))
    (tau : Fin r → CompleteIntersection H)
    (htau : Ideal.span (Set.range (fun i => q (tau i))) =
      IsLocalRing.maximalIdeal (ParameterRing r)) :
    Ideal.Quotient.mk (Ideal.span (Set.range tau)) (relativeJacobian H) ≠ 0 := by
  let : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨H', E, q', hEX, hH', hfinite, hfree, hq'⟩ :=
    completeIntersection_lifted_parameter_presentation H hr hc hH q hq tau htau
  let B := ParameterRing r
  let A := CompleteIntersection H
  let D := CompleteIntersection H'
  let : Module.Finite B D := hfinite
  let : Module.Free B D := hfree
  let : Module.Flat B D := Module.Flat.of_free
  obtain ⟨p⟩ := completeIntersection_parameter_pairing H' hr hc hH'
  have hgen := fun x => (lemma31_annihilator_conclusion H hr hc hH q hq x).mp
  have hd : Annihilates (nilradical A) (relativeJacobian H) :=
    (lemma31_annihilator_conclusion H hr hc hH q hq _).mpr ⟨1, by simp⟩
  let delta := E.symm (relativeJacobian H)
  have hdD : Annihilates (nilradical D) delta :=
    (annihilates_nilradical_ringEquiv E delta).mpr (by rw [E.apply_symm_apply]; exact hd)
  have hgenD : ∀ x : D, Annihilates (nilradical D) x → ∃ b : B, x = b • delta :=
    annihilator_scalar_generation_ringEquiv E q' hq' (relativeJacobian H) hd hgen
  have he : ∀ a : D, q' a = (RingEquiv.refl B) (q' a) := fun _ => rfl
  have hne := annihilator_generator_survives_new_parameterIdeal q' q' (RingEquiv.refl B)
    hq' he delta hdD hgenD p (fun i : Fin r => (MvPowerSeries.X i : B))
    (IsLocalRing.maximalIdeal B) (IsLocalRing.maximalIdeal.isMaximal B).ne_top
    (fun i => by
      rw [← powerSeries_coordinateIdeal_eq_maximalIdeal]
      exact Ideal.subset_span (Set.mem_range_self i))
  let J := Ideal.span (Set.range (fun i : Fin r => algebraMap B D (MvPowerSeries.X i)))
  have hJE : (Ideal.span (Set.range tau)) = J.map E.toRingHom := by
    rw [Ideal.map_span, ← Set.range_comp]
    change Ideal.span (Set.range tau) =
      Ideal.span (Set.range (fun i : Fin r => E (algebraMap B D (MvPowerSeries.X i))))
    rw [show (fun i : Fin r => E (algebraMap B D (MvPowerSeries.X i))) = tau from funext hEX]
  let EQ := Ideal.quotientEquiv J (Ideal.span (Set.range tau)) E hJE
  intro hz
  apply hne
  apply EQ.injective
  change EQ (Ideal.Quotient.mk J delta) = EQ 0
  rw [Ideal.quotientEquiv_mk, E.apply_symm_apply, map_zero]
  exact hz
end LinearStudy
