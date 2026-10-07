module
public import Linear.ProjectiveCoordinateRelabel
public import Linear.SmoothInvariantLocal
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n r c : ℕ} [Nonempty (Fin c)]

theorem projective_smooth_local_pullback_structure
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hf : 1 < f.degree) (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (e : Fin (n + 1) ≃ Fin r ⊕ Fin c) (hr : 0 < r) (hc : 0 < c)
    (P Q : Ideal (MvPolynomial (Fin r ⊕ Fin c) ℂ)) [P.IsPrime] [Q.IsPrime]
    (x : Fin r ⊕ Fin c → ℂ)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := ℂ) x).toRingHom)
    (G H : Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (hQ : Q = RingHom.ker (MvPolynomial.aeval (R := ℂ) (fun i =>
      MvPolynomial.eval x (MvPolynomial.renameEquiv ℂ e (f.forms (e.symm i))))).toRingHom)
    (hsource : (V.ideal.toIdeal.map (MvPolynomial.renameEquiv ℂ e).toRingHom).map
        (algebraMap _ (Localization.AtPrime P)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i))))
    (htarget : (V.ideal.toIdeal.map (MvPolynomial.renameEquiv ℂ e).toRingHom).map
        (algebraMap _ (Localization.AtPrime Q)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime Q) (H i)))) :
    let F := fun i => MvPolynomial.renameEquiv ℂ e (f.forms (e.symm i))
    let L := smoothPullbackEquations x G hG hJ F H
    RingTheory.Sequence.IsRegular (AmbientRing r c) (List.ofFn L) ∧
      Module.Finite (ParameterRing r) (CompleteIntersection L) ∧
      Module.Free (ParameterRing r) (CompleteIntersection L) := by
  apply smooth_invariant_local_pullback_structure hr hc
    (V.ideal.toIdeal.map (MvPolynomial.renameEquiv ℂ e).toRingHom) P Q x _ hP hQ
    (projective_total_invariance_relabel_radical f V (by omega) hV e)
    G H hG hJ hsource htarget

theorem projective_smooth_local_parameter_jacobian_socle
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hf : 1 < f.degree) (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (e : Fin (n + 1) ≃ Fin r ⊕ Fin c) (hr : 0 < r) (hc : 0 < c)
    (P Q : Ideal (MvPolynomial (Fin r ⊕ Fin c) ℂ)) [P.IsPrime] [Q.IsPrime]
    (x : Fin r ⊕ Fin c → ℂ)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := ℂ) x).toRingHom)
    (G H : Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (hQ : Q = RingHom.ker (MvPolynomial.aeval (R := ℂ) (fun i =>
      MvPolynomial.eval x (MvPolynomial.renameEquiv ℂ e (f.forms (e.symm i))))).toRingHom)
    (hsource : (V.ideal.toIdeal.map (MvPolynomial.renameEquiv ℂ e).toRingHom).map
        (algebraMap _ (Localization.AtPrime P)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i))))
    (htarget : (V.ideal.toIdeal.map (MvPolynomial.renameEquiv ℂ e).toRingHom).map
        (algebraMap _ (Localization.AtPrime Q)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime Q) (H i))))
    (τ : Fin r → AmbientRing r c)
    (hτ : Ideal.span (Set.range (fun i => (τ i).constantCoeff)) =
      IsLocalRing.maximalIdeal (ParameterRing r)) :
    let F := fun i => MvPolynomial.renameEquiv ℂ e (f.forms (e.symm i))
    let L := smoothPullbackEquations x G hG hJ F H
    let J := Ideal.span (Set.range (fun i => Ideal.Quotient.mk (equationIdeal L) (τ i)))
    let A := CompleteIntersection L ⧸ J
    let m := (nilradical (CompleteIntersection L)).map (Ideal.Quotient.mk J)
    IsArtinianRing A ∧ m.IsMaximal ∧
      m.annihilator = Ideal.span {Ideal.Quotient.mk J (relativeJacobian L)} ∧
      Ideal.Quotient.mk J (relativeJacobian L) ≠ 0 := by
  let F := fun i => MvPolynomial.renameEquiv ℂ e (f.forms (e.symm i))
  let L := smoothPullbackEquations x G hG hJ F H
  have hrad : (equationIdeal L).radical =
      Ideal.span (Set.range (MvPowerSeries.X (σ := Fin c) (R := ParameterRing r))) :=
    smooth_invariant_local_pullback_radical
      (V.ideal.toIdeal.map (MvPolynomial.renameEquiv ℂ e).toRingHom) P Q x F hP hQ
      (projective_total_invariance_relabel_radical f V (by omega) hV e)
      G H hG hJ hsource htarget
  have hlocal := formalThickening_relativeJacobian_socle L hr hc hrad
  apply hlocal.2 (fun i => Ideal.Quotient.mk (equationIdeal L) (τ i))
  change Ideal.span (Set.range (fun i => (τ i).constantCoeff)) = _
  exact hτ

end LinearStudy
