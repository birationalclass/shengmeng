module
public import Linear.PolynomialSmoothCoordinates
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K : Type*} [Field K] {r c : ℕ} [Nonempty (Fin c)]

def polynomialSmoothAmbientEquiv (x : Fin r ⊕ Fin c → K)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i))))) :
    MvPowerSeries (Fin r ⊕ Fin c) K ≃+*
      MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) :=
  (polynomialSmoothCoordinateEquiv x G hG hJ).symm.toRingEquiv.trans
    (powerSeriesCoordinateChart K r c).symm

theorem polynomialSmoothAmbientEquiv_polynomial (x : Fin r ⊕ Fin c → K)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (P : MvPolynomial (Fin r ⊕ Fin c) K) :
    polynomialSmoothAmbientEquiv x G hG hJ (formalPolynomialAtPoint x P) =
      polynomialSmoothFormalMap x G hG hJ P := rfl

def smoothPolynomialFormalFiberEquiv
    (I : Ideal (MvPolynomial (Fin r ⊕ Fin c) K))
    [IsArtinianRing (MvPolynomial (Fin r ⊕ Fin c) K ⧸ I)]
    (q : (MvPolynomial (Fin r ⊕ Fin c) K ⧸ I) →ₐ[K] K)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval
      (fun j => q (Ideal.Quotient.mk I (MvPolynomial.X j))) (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval
      (fun j => q (Ideal.Quotient.mk I (MvPolynomial.X j)))
      (MvPolynomial.pderiv (Sum.inr j) (G i))))) :
    letI : (RingHom.ker q.toRingHom).IsPrime := RingHom.ker_isPrime _
    let x := fun j => q (Ideal.Quotient.mk I (MvPolynomial.X j))
    (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) ⧸
      I.map (polynomialSmoothFormalMap x G hG hJ)) ≃+*
      Localization.AtPrime (RingHom.ker q.toRingHom) := by
  let : (RingHom.ker q.toRingHom).IsPrime := RingHom.ker_isPrime _
  let x := fun j => q (Ideal.Quotient.mk I (MvPolynomial.X j))
  let E := polynomialSmoothAmbientEquiv x G hG hJ
  have hmap : I.map (polynomialSmoothFormalMap x G hG hJ) =
      (formalPolynomialIdealAtPoint I x).map E.toRingHom := by
    rw [formalPolynomialIdealAtPoint, Ideal.map_map]
    rfl
  exact (Ideal.quotientEquiv _ _ E hmap).symm.trans
    (polynomialFormalFiberEquiv I q)

theorem smoothPolynomialFormalFiberEquiv_polynomial
    (I : Ideal (MvPolynomial (Fin r ⊕ Fin c) K))
    [IsArtinianRing (MvPolynomial (Fin r ⊕ Fin c) K ⧸ I)]
    (q : (MvPolynomial (Fin r ⊕ Fin c) K ⧸ I) →ₐ[K] K)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval
      (fun j => q (Ideal.Quotient.mk I (MvPolynomial.X j))) (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval
      (fun j => q (Ideal.Quotient.mk I (MvPolynomial.X j)))
      (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (P : MvPolynomial (Fin r ⊕ Fin c) K) :
    letI : (RingHom.ker q.toRingHom).IsPrime := RingHom.ker_isPrime _
    let x := fun j => q (Ideal.Quotient.mk I (MvPolynomial.X j))
    smoothPolynomialFormalFiberEquiv I q G hG hJ
      (Ideal.Quotient.mk _ (polynomialSmoothFormalMap x G hG hJ P)) =
      algebraMap (MvPolynomial (Fin r ⊕ Fin c) K ⧸ I)
        (Localization.AtPrime (RingHom.ker q.toRingHom)) (Ideal.Quotient.mk I P) := by
  let : (RingHom.ker q.toRingHom).IsPrime := RingHom.ker_isPrime _
  dsimp only [smoothPolynomialFormalFiberEquiv]
  rw [RingEquiv.trans_apply, Ideal.quotientEquiv_symm_mk]
  rw [← polynomialSmoothAmbientEquiv_polynomial, RingEquiv.symm_apply_apply]
  exact polynomialFormalFiberEquiv_polynomial I q P

theorem smooth_polynomial_formal_socle_generator_descends
    (I : Ideal (MvPolynomial (Fin r ⊕ Fin c) K))
    [IsArtinianRing (MvPolynomial (Fin r ⊕ Fin c) K ⧸ I)]
    (q : (MvPolynomial (Fin r ⊕ Fin c) K ⧸ I) →ₐ[K] K)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval
      (fun j => q (Ideal.Quotient.mk I (MvPolynomial.X j))) (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval
      (fun j => q (Ideal.Quotient.mk I (MvPolynomial.X j)))
      (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (theta : MvPolynomial (Fin r ⊕ Fin c) K)
    (h : let x := fun j => q (Ideal.Quotient.mk I (MvPolynomial.X j))
      let A := MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) ⧸
        I.map (polynomialSmoothFormalMap x G hG hJ)
      (nilradical A).annihilator = Ideal.span
        {Ideal.Quotient.mk _ (polynomialSmoothFormalMap x G hG hJ theta)}) :
    letI : (RingHom.ker q.toRingHom).IsPrime := RingHom.ker_isPrime _
    (nilradical (Localization.AtPrime (RingHom.ker q.toRingHom))).annihilator =
      Ideal.span (Set.singleton (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K ⧸ I)
        (Localization.AtPrime (RingHom.ker q.toRingHom)) (Ideal.Quotient.mk I theta))) := by
  let : (RingHom.ker q.toRingHom).IsPrime := RingHom.ker_isPrime _
  let x := fun j => q (Ideal.Quotient.mk I (MvPolynomial.X j))
  let A := MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) ⧸
    I.map (polynomialSmoothFormalMap x G hG hJ)
  let E : A ≃+* Localization.AtPrime (RingHom.ker q.toRingHom) :=
    smoothPolynomialFormalFiberEquiv I q G hG hJ
  have hg := ringEquiv_nilradical_annihilator_generator (A := A)
    (C := Localization.AtPrime (RingHom.ker q.toRingHom)) E
    (Ideal.Quotient.mk _ (polynomialSmoothFormalMap x G hG hJ theta)) h
  dsimp only [E] at hg
  rwa [smoothPolynomialFormalFiberEquiv_polynomial] at hg

end LinearStudy
