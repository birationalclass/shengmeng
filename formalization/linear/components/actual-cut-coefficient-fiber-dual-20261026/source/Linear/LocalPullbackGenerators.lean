module
public import Linear.PolynomialSmoothCoordinates
public import Mathlib.RingTheory.Localization.AtPrime.Basic
/-! Target point-local generators transfer along the actual polynomial pullback
into constructed smooth source formal coordinates. Localization denominators
are proved invertible from actual point evaluation. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

theorem local_ideal_generators_image
    {R S ι : Type*} [CommRing R] [CommRing S]
    (I P : Ideal R) [P.IsPrime] (G : ι → R) (ψ : R →+* S)
    (hunit : ∀ s : P.primeCompl, IsUnit (ψ s))
    (hlocal : I.map (algebraMap R (Localization.AtPrime P)) =
      Ideal.span (Set.range (fun i => algebraMap R (Localization.AtPrime P) (G i)))) :
    I.map ψ = Ideal.span (Set.range (fun i => ψ (G i))) := by
  let χ : Localization.AtPrime P →+* S := IsLocalization.lift hunit
  have hχ : χ.comp (algebraMap R (Localization.AtPrime P)) = ψ := IsLocalization.lift_comp hunit
  have h := congrArg (fun J : Ideal (Localization.AtPrime P) => J.map χ) hlocal
  rw [Ideal.map_map, hχ, Ideal.map_span, ← Set.range_comp] at h
  change I.map ψ = Ideal.span (Set.range (fun i => χ (algebraMap R (Localization.AtPrime P) (G i)))) at h
  have hfun : (fun i => χ (algebraMap R (Localization.AtPrime P) (G i))) =
      (fun i => ψ (G i)) := funext (fun i => IsLocalization.lift_eq hunit (G i))
  rwa [hfun] at h

variable {K : Type*} [Field K] {r c : ℕ} [Nonempty (Fin c)]

theorem polynomialSmoothFormalMap_isUnit_iff (x : Fin r ⊕ Fin c → K)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (P : MvPolynomial (Fin r ⊕ Fin c) K) :
    IsUnit (polynomialSmoothFormalMap x G hG hJ P) ↔ MvPolynomial.eval x P ≠ 0 := by
  let E := polynomialSmoothCoordinateEquiv x G hG hJ
  change IsUnit ((powerSeriesCoordinateChart K r c).symm (E.symm (formalPolynomialAtPoint x P))) ↔ _
  rw [isUnit_map_iff (powerSeriesCoordinateChart K r c).symm, isUnit_map_iff E.symm,
    MvPowerSeries.isUnit_iff_constantCoeff, formalPolynomialAtPoint_constantCoeff, isUnit_iff_ne_zero]

theorem polynomialSmoothFormalMap_target_local_generators
    (x : Fin r ⊕ Fin c → K)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (F : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (I P : Ideal (MvPolynomial (Fin r ⊕ Fin c) K)) [P.IsPrime]
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) (fun i => MvPolynomial.eval x (F i))).toRingHom)
    {ι : Type*} (H : ι → MvPolynomial (Fin r ⊕ Fin c) K)
    (hlocal : I.map (algebraMap _ (Localization.AtPrime P)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (H i)))) :
    (I.map (MvPolynomial.aeval F).toRingHom).map (polynomialSmoothFormalMap x G hG hJ) =
      Ideal.span (Set.range (fun i => polynomialSmoothFormalMap x G hG hJ (MvPolynomial.aeval F (H i)))) := by
  rw [Ideal.map_map]
  apply local_ideal_generators_image I P H
  · intro s
    apply (polynomialSmoothFormalMap_isUnit_iff x G hG hJ _).mpr
    change MvPolynomial.eval x (MvPolynomial.eval₂ MvPolynomial.C F s) ≠ 0
    rw [← MvPolynomial.eval_assoc]
    have hs : (s : MvPolynomial (Fin r ⊕ Fin c) K) ∉ P := s.property
    intro hz
    apply hs
    exact (congrArg (fun J : Ideal (MvPolynomial (Fin r ⊕ Fin c) K) =>
      (s : MvPolynomial (Fin r ⊕ Fin c) K) ∈ J) hP).mpr hz
  · exact hlocal

end LinearStudy
