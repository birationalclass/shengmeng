module
public import Linear.PolynomialFormalDerivative
public import Linear.SmoothFormalQuotient
/-! Construct actual smooth point formal coordinates from a polynomial
Jacobian minor and point-local generators. No opaque formal coordinate map
or normal-ideal identification is assumed. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K : Type*} [Field K] {r c : ℕ} [Nonempty (Fin c)]

def polynomialSmoothCoordinateEquiv (x : Fin r ⊕ Fin c → K)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i))))) :
    MvPowerSeries (Fin r ⊕ Fin c) K ≃ₐ[K] MvPowerSeries (Fin r ⊕ Fin c) K :=
  smoothFormalCoordinateEquiv (fun i => formalPolynomialAtPoint x (G i))
    (fun i => by rw [formalPolynomialAtPoint_constantCoeff]; exact hG i)
    (by simpa only [formalPolynomialAtPoint_pderiv, formalPolynomialAtPoint_constantCoeff] using hJ)

def polynomialSmoothFormalMap (x : Fin r ⊕ Fin c → K)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i))))) :
    MvPolynomial (Fin r ⊕ Fin c) K →+* MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) :=
  (powerSeriesCoordinateChart K r c).symm.toRingHom.comp
    ((polynomialSmoothCoordinateEquiv x G hG hJ).symm.toRingEquiv.toRingHom.comp
      (formalPolynomialAtPoint x))

theorem polynomialSmoothFormalMap_equation (x : Fin r ⊕ Fin c → K)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (i : Fin c) :
    polynomialSmoothFormalMap x G hG hJ (G i) = MvPowerSeries.X i := by
  let E := polynomialSmoothCoordinateEquiv x G hG hJ
  change (powerSeriesCoordinateChart K r c).symm (E.symm (formalPolynomialAtPoint x (G i))) = _
  have hE : E (MvPowerSeries.X (Sum.inr i)) = formalPolynomialAtPoint x (G i) :=
    smoothFormalCoordinateEquiv_normal _ _ _ i
  rw [← hE, AlgEquiv.symm_apply_apply, ← powerSeriesCoordinateChart_X K r c i,
    RingEquiv.symm_apply_apply]

theorem polynomialSmoothFormalMap_parameter (x : Fin r ⊕ Fin c → K)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (i : Fin r) :
    polynomialSmoothFormalMap x G hG hJ (MvPolynomial.X (Sum.inl i) - MvPolynomial.C (x (Sum.inl i))) =
      MvPowerSeries.C (MvPowerSeries.X i) := by
  let E := polynomialSmoothCoordinateEquiv x G hG hJ
  change (powerSeriesCoordinateChart K r c).symm
    (E.symm (formalPolynomialAtPoint x (MvPolynomial.X (Sum.inl i) - MvPolynomial.C (x (Sum.inl i))))) = _
  rw [formalPolynomialAtPoint_centered_X]
  have hE : E (MvPowerSeries.X (Sum.inl i)) = MvPowerSeries.X (Sum.inl i) :=
    smoothFormalCoordinateEquiv_parameter _ _ _ i
  rw [← hE, AlgEquiv.symm_apply_apply]
  apply (powerSeriesCoordinateChart K r c).injective
  rw [RingEquiv.apply_symm_apply, powerSeriesCoordinateChart_C, MvPowerSeries.rename_X]

theorem polynomialSmoothFormalMap_ideal (I : Ideal (MvPolynomial (Fin r ⊕ Fin c) K))
    (x : Fin r ⊕ Fin c → K)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (hI : I.map (formalPolynomialAtPoint x) = Ideal.span (Set.range (fun i => formalPolynomialAtPoint x (G i)))) :
    I.map (polynomialSmoothFormalMap x G hG hJ) =
      Ideal.span (Set.range (MvPowerSeries.X (σ := Fin c) (R := MvPowerSeries (Fin r) K))) := by
  let E := polynomialSmoothCoordinateEquiv x G hG hJ
  let χ := (powerSeriesCoordinateChart K r c).symm.toRingHom.comp E.symm.toRingEquiv.toRingHom
  have hmap : I.map (polynomialSmoothFormalMap x G hG hJ) = (I.map (formalPolynomialAtPoint x)).map χ := by
    rw [Ideal.map_map]
    rfl
  rw [hmap, hI, Ideal.map_span, ← Set.range_comp]
  have hfun : (χ ∘ fun i => formalPolynomialAtPoint x (G i)) =
      (MvPowerSeries.X (σ := Fin c) (R := MvPowerSeries (Fin r) K)) := by
    funext i
    exact polynomialSmoothFormalMap_equation x G hG hJ i
  rw [hfun]

theorem polynomialSmoothFormalMap_local_ideal
    (I P : Ideal (MvPolynomial (Fin r ⊕ Fin c) K)) [P.IsPrime]
    (x : Fin r ⊕ Fin c → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (hlocal : I.map (algebraMap _ (Localization.AtPrime P)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i)))) :
    I.map (polynomialSmoothFormalMap x G hG hJ) =
      Ideal.span (Set.range (MvPowerSeries.X (σ := Fin c) (R := MvPowerSeries (Fin r) K))) :=
  polynomialSmoothFormalMap_ideal I x G hG hJ
    (formalPolynomialIdeal_local_generators I P x hP G hlocal)

end LinearStudy
