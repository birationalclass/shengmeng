module
public import Linear.ProjectiveIdealInvariance
public import Linear.ThickeningFromRadical
/-! Compose original projective total invariance with actual formal ideal
identifications to derive regular finite free structure and parameter socles.
Smooth coordinate identifications and etale parameter generation are explicit
remaining inputs, not claimed as consequences here. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] NoZeroDivisors.to_isDomain
attribute [local instance] MvPolynomial.gradedAlgebra

theorem projective_invariant_formal_radical
    {n r c : ℕ} (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hf : 1 < f.degree) (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (ψ : CoordinateRing n →+* AmbientRing r c) (hc : 0 < c)
    (H : Fin c → AmbientRing r c)
    (hcoord : V.ideal.toIdeal.map ψ =
      Ideal.span (Set.range (MvPowerSeries.X (σ := Fin c) (R := ParameterRing r))))
    (hH : (V.ideal.toIdeal.map (MvPolynomial.aeval f.forms).toRingHom).map ψ = equationIdeal H) :
    (equationIdeal H).radical =
      Ideal.span (Set.range (MvPowerSeries.X (σ := Fin c) (R := ParameterRing r))) := by
  let : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
  obtain ⟨e, he, hlower, hupper⟩ := projective_total_invariance_formal_sandwich f V
    (by omega) hV ψ
  rw [hcoord, hH] at hlower hupper
  exact powerSeries_thickening_radical _ e he hupper hlower

theorem projective_invariant_formal_structure
    {n r c : ℕ} (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hf : 1 < f.degree) (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (ψ : CoordinateRing n →+* AmbientRing r c) (hr : 0 < r) (hc : 0 < c)
    (H : Fin c → AmbientRing r c)
    (hcoord : V.ideal.toIdeal.map ψ =
      Ideal.span (Set.range (MvPowerSeries.X (σ := Fin c) (R := ParameterRing r))))
    (hH : (V.ideal.toIdeal.map (MvPolynomial.aeval f.forms).toRingHom).map ψ = equationIdeal H) :
    RingTheory.Sequence.IsRegular (AmbientRing r c) (List.ofFn H) ∧
      Module.Finite (ParameterRing r) (CompleteIntersection H) ∧
      Module.Free (ParameterRing r) (CompleteIntersection H) :=
  powerSeries_thickening_structure_from_radical r c hr hc H
    (projective_invariant_formal_radical f V hf hV ψ hc H hcoord hH)

theorem projective_invariant_formal_parameter_jacobian_socle
    {n r c : ℕ} (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hf : 1 < f.degree) (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (ψ : CoordinateRing n →+* AmbientRing r c) (hr : 0 < r) (hc : 0 < c)
    (H : Fin c → AmbientRing r c)
    (hcoord : V.ideal.toIdeal.map ψ =
      Ideal.span (Set.range (MvPowerSeries.X (σ := Fin c) (R := ParameterRing r))))
    (hH : (V.ideal.toIdeal.map (MvPolynomial.aeval f.forms).toRingHom).map ψ = equationIdeal H)
    (τ : Fin r → AmbientRing r c)
    (hτ : Ideal.span (Set.range (fun i => (τ i).constantCoeff)) =
      IsLocalRing.maximalIdeal (ParameterRing r)) :
    let J := Ideal.span (Set.range (fun i => Ideal.Quotient.mk (equationIdeal H) (τ i)))
    let Q := CompleteIntersection H ⧸ J
    let m := (nilradical (CompleteIntersection H)).map (Ideal.Quotient.mk J)
    IsArtinianRing Q ∧ m.IsMaximal ∧
      m.annihilator = Ideal.span {Ideal.Quotient.mk J (relativeJacobian H)} ∧
      Ideal.Quotient.mk J (relativeJacobian H) ≠ 0 := by
  have hrad := projective_invariant_formal_radical f V hf hV ψ hc H hcoord hH
  have hlocal := formalThickening_relativeJacobian_socle H hr hc hrad
  apply hlocal.2 (fun i => Ideal.Quotient.mk (equationIdeal H) (τ i))
  change Ideal.span (Set.range (fun i => (τ i).constantCoeff)) = _
  exact hτ

end LinearStudy
