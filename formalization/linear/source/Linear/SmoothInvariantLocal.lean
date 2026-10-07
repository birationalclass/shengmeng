module
public import Linear.LocalPullbackGenerators
public import Linear.ThickeningFromRadical
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] NoZeroDivisors.to_isDomain
variable {K : Type*} [Field K] {r c : ℕ} [Nonempty (Fin c)]

def smoothPullbackEquations (x : Fin r ⊕ Fin c → K)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (F : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (H : Fin c → MvPolynomial (Fin r ⊕ Fin c) K) :
    Fin c → MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) :=
  fun i => polynomialSmoothFormalMap x G hG hJ (MvPolynomial.aeval F (H i))

theorem smooth_invariant_local_pullback_radical
    (I P Q : Ideal (MvPolynomial (Fin r ⊕ Fin c) K)) [P.IsPrime] [Q.IsPrime]
    (x : Fin r ⊕ Fin c → K)
    (F : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (hQ : Q = RingHom.ker (MvPolynomial.aeval (R := K) (fun i => MvPolynomial.eval x (F i))).toRingHom)
    (hrad : (I.map (MvPolynomial.aeval F).toRingHom).radical = I)
    (G H : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (hsource : I.map (algebraMap _ (Localization.AtPrime P)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i))))
    (htarget : I.map (algebraMap _ (Localization.AtPrime Q)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime Q) (H i)))) :
    (Ideal.span (Set.range (smoothPullbackEquations x G hG hJ F H))).radical =
      Ideal.span (Set.range (MvPowerSeries.X (σ := Fin c) (R := MvPowerSeries (Fin r) K))) := by
  let ψ := polynomialSmoothFormalMap x G hG hJ
  let J := I.map (MvPolynomial.aeval F).toRingHom
  have hsource' := polynomialSmoothFormalMap_local_ideal I P x hP G hG hJ hsource
  have htarget' := polynomialSmoothFormalMap_target_local_generators x G hG hJ F I Q hQ H htarget
  have hupper : J ≤ I := by
    have h : J ≤ J.radical := Ideal.le_radical
    rwa [hrad] at h
  obtain ⟨e, he⟩ := J.exists_radical_pow_le_of_fg (IsNoetherian.noetherian _)
  have hlower : I ^ (e + 1) ≤ J := by
    have h : J.radical ^ (e + 1) ≤ J := (Ideal.pow_le_pow_right (Nat.le_succ e)).trans he
    rwa [hrad] at h
  have hu := Ideal.map_mono (f := ψ) hupper
  have hl := Ideal.map_mono (f := ψ) hlower
  rw [Ideal.map_pow] at hl
  change J.map ψ = Ideal.span (Set.range (smoothPullbackEquations x G hG hJ F H)) at htarget'
  rw [htarget', hsource'] at hu hl
  exact powerSeries_thickening_radical _ (e + 1) (Nat.zero_lt_succ _) hu hl

theorem smooth_invariant_local_pullback_structure
    (hr : 0 < r) (hc : 0 < c)
    (I P Q : Ideal (MvPolynomial (Fin r ⊕ Fin c) K)) [P.IsPrime] [Q.IsPrime]
    (x : Fin r ⊕ Fin c → K)
    (F : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (hQ : Q = RingHom.ker (MvPolynomial.aeval (R := K) (fun i => MvPolynomial.eval x (F i))).toRingHom)
    (hrad : (I.map (MvPolynomial.aeval F).toRingHom).radical = I)
    (G H : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (hsource : I.map (algebraMap _ (Localization.AtPrime P)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i))))
    (htarget : I.map (algebraMap _ (Localization.AtPrime Q)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime Q) (H i)))) :
    let L := smoothPullbackEquations x G hG hJ F H
    RingTheory.Sequence.IsRegular (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K)) (List.ofFn L) ∧
      Module.Finite (MvPowerSeries (Fin r) K)
        (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) ⧸ Ideal.span (Set.range L)) ∧
      Module.Free (MvPowerSeries (Fin r) K)
        (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) ⧸ Ideal.span (Set.range L)) :=
  powerSeries_thickening_structure_from_radical r c hr hc _
    (smooth_invariant_local_pullback_radical I P Q x F hP hQ hrad G H hG hJ hsource htarget)

end LinearStudy
