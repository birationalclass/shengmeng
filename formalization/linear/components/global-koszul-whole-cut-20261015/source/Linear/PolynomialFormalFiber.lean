module
public import Linear.PolynomialPointCompletion
public import Linear.LocalFiber
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K σ : Type*} [Field K] [Finite σ]
attribute [local instance] polynomial_idealOfVars_isMaximal

def formalPolynomialAtPoint (x : σ → K) :
    MvPolynomial σ K →+* MvPowerSeries σ K :=
  MvPolynomial.coeToMvPowerSeries.ringHom.comp (polynomialTranslation x).toRingHom

def formalPolynomialIdealAtPoint (I : Ideal (MvPolynomial σ K)) (x : σ → K) :
    Ideal (MvPowerSeries σ K) := I.map (formalPolynomialAtPoint x)

def polynomialPrimeFormalCompletionEquiv (P : Ideal (MvPolynomial σ K)) [P.IsPrime]
    (x : σ → K) (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom) :
    MvPowerSeries σ K ≃+* AdicCompletion
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P) := by
  subst P
  exact polynomialPointFormalCompletionEquiv x

theorem polynomialPrimeFormalCompletionEquiv_polynomial
    (P : Ideal (MvPolynomial σ K)) [P.IsPrime]
    (x : σ → K) (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (f : MvPolynomial σ K) :
    polynomialPrimeFormalCompletionEquiv P x hP (formalPolynomialAtPoint x f) =
      algebraMap (Localization.AtPrime P)
        (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P))
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime P) f) := by
  subst P
  exact polynomialPointFormalCompletionEquiv_polynomial x f

omit [Finite σ] in
theorem polynomial_residue_point_kernel (I : Ideal (MvPolynomial σ K))
    (q : (MvPolynomial σ K ⧸ I) →ₐ[K] K) :
    (RingHom.ker q.toRingHom).comap (Ideal.Quotient.mk I) =
      RingHom.ker (MvPolynomial.aeval (R := K)
        (fun i => q (Ideal.Quotient.mk I (MvPolynomial.X i)))).toRingHom := by
  have he : q.comp (Ideal.Quotient.mkₐ K I) =
      MvPolynomial.aeval (R := K) (fun i => q (Ideal.Quotient.mk I (MvPolynomial.X i))) := by
    ext i
    simp
  ext f
  change q (Ideal.Quotient.mk I f) = 0 ↔ MvPolynomial.aeval _ f = 0
  rw [← he]
  rfl

def polynomialFormalFiberEquiv (I : Ideal (MvPolynomial σ K))
    [IsArtinianRing (MvPolynomial σ K ⧸ I)]
    (q : (MvPolynomial σ K ⧸ I) →ₐ[K] K) :
    letI : (RingHom.ker q.toRingHom).IsPrime := RingHom.ker_isPrime _
    let x := fun i => q (Ideal.Quotient.mk I (MvPolynomial.X i))
    (MvPowerSeries σ K ⧸ formalPolynomialIdealAtPoint I x) ≃+*
      Localization.AtPrime (RingHom.ker q.toRingHom) := by
  let : (RingHom.ker q.toRingHom).IsPrime := RingHom.ker_isPrime _
  let x := fun i => q (Ideal.Quotient.mk I (MvPolynomial.X i))
  let P := (RingHom.ker q.toRingHom).comap (Ideal.Quotient.mk I)
  let A := Localization.AtPrime P
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let E := polynomialPrimeFormalCompletionEquiv P x (polynomial_residue_point_kernel I q)
  let J := (I.map (algebraMap (MvPolynomial σ K) A)).map (algebraMap A C)
  have he : (E : _ →+* _).comp (formalPolynomialAtPoint x) =
      (algebraMap A C).comp (algebraMap (MvPolynomial σ K) A) := by
    apply RingHom.ext; intro f
    exact polynomialPrimeFormalCompletionEquiv_polynomial P x _ f
  have hm : J = (formalPolynomialIdealAtPoint I x).map (E : _ →+* _) := by
    rw [formalPolynomialIdealAtPoint, Ideal.map_map, he]
    rw [← Ideal.map_map]
  exact (Ideal.quotientEquiv (formalPolynomialIdealAtPoint I x) J E hm).trans
    (localFiberCompletionQuotientEquiv I (RingHom.ker q.toRingHom))

theorem polynomialFormalFiberEquiv_polynomial (I : Ideal (MvPolynomial σ K))
    [IsArtinianRing (MvPolynomial σ K ⧸ I)]
    (q : (MvPolynomial σ K ⧸ I) →ₐ[K] K) (f : MvPolynomial σ K) :
    letI : (RingHom.ker q.toRingHom).IsPrime := RingHom.ker_isPrime _
    let x := fun i => q (Ideal.Quotient.mk I (MvPolynomial.X i))
    polynomialFormalFiberEquiv I q (Ideal.Quotient.mk _ (formalPolynomialAtPoint x f)) =
      algebraMap (MvPolynomial σ K ⧸ I) (Localization.AtPrime (RingHom.ker q.toRingHom))
        (Ideal.Quotient.mk I f) := by
  let : (RingHom.ker q.toRingHom).IsPrime := RingHom.ker_isPrime _
  dsimp only [polynomialFormalFiberEquiv]
  rw [RingEquiv.trans_apply, Ideal.quotientEquiv_mk,
    polynomialPrimeFormalCompletionEquiv_polynomial, localFiberCompletionQuotientEquiv_mk]

theorem polynomial_formal_socle_generator_descends
    (I : Ideal (MvPolynomial σ K)) [IsArtinianRing (MvPolynomial σ K ⧸ I)]
    (q : (MvPolynomial σ K ⧸ I) →ₐ[K] K) (theta : MvPolynomial σ K)
    (h : let x := fun i => q (Ideal.Quotient.mk I (MvPolynomial.X i))
      let B := MvPowerSeries σ K ⧸ formalPolynomialIdealAtPoint I x
      (nilradical B).annihilator = Ideal.span {Ideal.Quotient.mk _ (formalPolynomialAtPoint x theta)}) :
    letI : (RingHom.ker q.toRingHom).IsPrime := RingHom.ker_isPrime _
    (nilradical (Localization.AtPrime (RingHom.ker q.toRingHom))).annihilator =
      Ideal.span (Set.singleton (algebraMap (MvPolynomial σ K ⧸ I)
        (Localization.AtPrime (RingHom.ker q.toRingHom)) (Ideal.Quotient.mk I theta))) := by
  let : (RingHom.ker q.toRingHom).IsPrime := RingHom.ker_isPrime _
  let x : σ → K := fun i => q (Ideal.Quotient.mk I (MvPolynomial.X i))
  let B := MvPowerSeries σ K ⧸ formalPolynomialIdealAtPoint I x
  let E : B ≃+* Localization.AtPrime (RingHom.ker q.toRingHom) := polynomialFormalFiberEquiv I q
  have hg := ringEquiv_nilradical_annihilator_generator (A := B)
    (C := Localization.AtPrime (RingHom.ker q.toRingHom)) E
    (Ideal.Quotient.mk _ (formalPolynomialAtPoint x theta)) h
  dsimp only [E] at hg
  rwa [polynomialFormalFiberEquiv_polynomial] at hg

end LinearStudy
