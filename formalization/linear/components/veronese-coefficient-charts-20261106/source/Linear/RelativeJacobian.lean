module
public import Linear.CenteredRelativeJacobian
public import Linear.PowerSeriesCentering
public import Linear.CompleteIntersectionChange
public import Linear.FirstJet
public import Linear.Target
/-!
# Relative Jacobian generation without an extra centering hypothesis

Construct the actual parameter-algebra coordinate translation, change the
equations by its inverse, apply the centered theorem, and transport the actual
derivative determinant back. No perfect pairing, primitive generator or
vanishing of the normal coordinates is an input. Arbitrary parameter lifts
and the global geometric theorem remain separate unfinished obligations.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace LinearStudy
variable {K : Type*} [Field K] [CharZero K] {r n : ℕ}

theorem finiteFlat_jacobian_annihilator
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
    (x : MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) K) ⧸ Ideal.span (Set.range H)) :
    Annihilates (nilradical
      (MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) K) ⧸ Ideal.span (Set.range H))) x ↔
      ∃ u : MvPowerSeries (Fin (r + 1)) K,
        x = u • Ideal.Quotient.mk (Ideal.span (Set.range H))
          (Matrix.det (fun i j => MvPowerSeries.pderiv j (H i))) := by
  let B := MvPowerSeries (Fin (r + 1)) K
  let R := MvPowerSeries (Fin (n + 1)) B
  let I := Ideal.span (Set.range H)
  let aR : R →ₐ[B] B := a.comp (Ideal.Quotient.mkₐ B I)
  let e := powerSeriesCentering aR
  let H' := fun i => e.symm (H i)
  let I' := Ideal.span (Set.range H')
  let E : (R ⧸ I') ≃ₐ[B] (R ⧸ I) := (equationChangeQuotientEquiv e.symm H).symm
  let a' : (R ⧸ I') →ₐ[B] B := a.comp E.toAlgHom
  let : Module.Finite B (R ⧸ I') := equationChangeQuotient_finite e.symm H
  let : Module.Flat B (R ⧸ I') := equationChangeQuotient_flat e.symm H
  have hH' : RingTheory.Sequence.IsRegular R (List.ofFn H') := by
    rw [show List.ofFn H' = (List.ofFn H).map e.symm by rw [List.map_ofFn]; rfl]
    exact (regularSequence_change_equations e.symm (List.ofFn H)).mp hH
  have ha' : RingHom.ker a'.toRingHom = nilradical (R ⧸ I') :=
    nilradical_kernel_transport E a ha
  have hmk (z : R) : E (Ideal.Quotient.mk I' z) = Ideal.Quotient.mk I (e z) := by
    apply (equationChangeQuotientEquiv e.symm H).injective
    rw [AlgEquiv.apply_symm_apply, equationChangeQuotientEquiv_mk,
      AlgEquiv.symm_apply_apply]
  have hz (i : Fin (n + 1)) : a' (Ideal.Quotient.mk I' (MvPowerSeries.X i)) = 0 := by
    change a (E (Ideal.Quotient.mk I' (MvPowerSeries.X i))) = 0
    rw [hmk]
    exact powerSeriesCentering_coordinate_reduction_zero aR i
  have hδ : E (Ideal.Quotient.mk I'
      (Matrix.det (fun i j => MvPowerSeries.pderiv j (H' i)))) =
      Ideal.Quotient.mk I (Matrix.det (fun i j => MvPowerSeries.pderiv j (H i))) := by
    rw [hmk]
    change Ideal.Quotient.mk I (e (Matrix.det (fun i j => MvPowerSeries.pderiv j (e.symm (H i))))) = _
    rw [← powerSeriesCentering_symm_jacobian aR H, AlgEquiv.apply_symm_apply]
  have hx := finiteFlat_centered_jacobian_annihilator H' hH' a' ha' hz (E.symm x)
  rw [annihilates_nilradical_algEquiv B E, AlgEquiv.apply_symm_apply] at hx
  rw [hx]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    have h := congrArg E hu
    change E (E.symm x) = E (u • Ideal.Quotient.mk I'
      (Matrix.det (fun i j => MvPowerSeries.pderiv j (H' i)))) at h
    rw [AlgEquiv.apply_symm_apply, map_smul, hδ] at h
    exact h
  · rintro ⟨u, hu⟩
    refine ⟨u, E.injective ?_⟩
    rw [AlgEquiv.apply_symm_apply, map_smul, hδ]
    exact hu

/-- The first conjunct of the manuscript target, in its original notation. -/
theorem lemma31_annihilator_conclusion {r c : ℕ} (H : Fin c → AmbientRing r c)
    (hr : 0 < r) (hc : 0 < c)
    (hH : RingTheory.Sequence.IsRegular (AmbientRing r c) (List.ofFn H))
    [Module.Finite (ParameterRing r) (CompleteIntersection H)]
    [Module.Flat (ParameterRing r) (CompleteIntersection H)]
    (q : CompleteIntersection H →ₐ[ParameterRing r] ParameterRing r)
    (hq : RingHom.ker q.toRingHom = nilradical (CompleteIntersection H))
    (x : CompleteIntersection H) :
    Annihilates (nilradical (CompleteIntersection H)) x ↔
      ∃ b : ParameterRing r, x = b • relativeJacobian H := by
  dsimp only [CompleteIntersection, equationIdeal, AmbientRing, ParameterRing,
    relativeJacobian] at *
  cases r with
  | zero => exact False.elim (Nat.not_lt_zero _ hr)
  | succ r =>
    cases c with
    | zero => exact False.elim (Nat.not_lt_zero _ hc)
    | succ n => exact finiteFlat_jacobian_annihilator H hH q hq x
end LinearStudy
