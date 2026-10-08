module
public import Linear.ProjectiveCenteredFiberIdeal
public import Linear.PolynomialGlobalResidue
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy

theorem localized_annihilator_generator_at_equal_primes {R : Type*} [CommRing R]
    (u : R) (P Q : Ideal R) [P.IsPrime] [Q.IsPrime] (hPQ : P = Q)
    (h : (nilradical (Localization.AtPrime P)).annihilator =
      Ideal.span {algebraMap R (Localization.AtPrime P) u} ∧
        algebraMap R (Localization.AtPrime P) u ≠ 0) :
    (nilradical (Localization.AtPrime Q)).annihilator =
      Ideal.span {algebraMap R (Localization.AtPrime Q) u} ∧
        algebraMap R (Localization.AtPrime Q) u ≠ 0 := by
  subst Q
  exact h

/-- The SAME polynomial local generator at every original equation point
covers EVERY maximal ideal of the actual changed ambient equation algebra.
The actual original point and its quotient evaluation are constructed. -/
theorem polynomial_coordinate_socles_cover_maximal_ideals
    {K σ τ : Type*} [Field K] [IsAlgClosed K]
    (E : MvPolynomial σ K ≃ₐ[K] MvPolynomial τ K)
    (I : Ideal (MvPolynomial σ K)) (J : Ideal (MvPolynomial τ K))
    (hJ : J = I.map E.toRingHom) (Θ : MvPolynomial τ K)
    [Module.Finite K (MvPolynomial τ K ⧸ J)]
    (hloc : ∀ x : MvPolynomial.zeroLocus K I,
      ∃ q : (MvPolynomial τ K ⧸ J) →ₐ[K] K,
        (fun i => MvPolynomial.eval x.val (E.symm (MvPolynomial.X i))) =
          (fun i => q (Ideal.Quotient.mk J (MvPolynomial.X i))) ∧
        letI : (RingHom.ker q.toRingHom).IsPrime := RingHom.ker_isPrime _
        let t := algebraMap (MvPolynomial τ K ⧸ J)
          (Localization.AtPrime (RingHom.ker q.toRingHom)) (Ideal.Quotient.mk J Θ)
        (nilradical (Localization.AtPrime (RingHom.ker q.toRingHom))).annihilator =
          Ideal.span {t} ∧ t ≠ 0) :
    ∀ (L : Ideal (MvPolynomial τ K ⧸ J)) [L.IsMaximal],
      let t := algebraMap (MvPolynomial τ K ⧸ J) (Localization.AtPrime L) (Ideal.Quotient.mk J Θ)
      (nilradical (Localization.AtPrime L)).annihilator =
        Ideal.span {t} ∧ t ≠ 0 := by
  intro L hL
  let A := MvPolynomial τ K ⧸ J
  obtain ⟨q,hq⟩ := exists_maximalResidueMap (K := K) (A := A) ⟨L,hL⟩
  let u := fun j => q (Ideal.Quotient.mk J (MvPolynomial.X j))
  let x := fun i => MvPolynomial.eval u (E (MvPolynomial.X i))
  have hx := polynomial_quotient_coordinate_actual_zero E I J hJ q
  obtain ⟨q0,hpoint,hAnn⟩ := hloc ⟨x,hx.1⟩
  have hsame : q0 = q := by
    apply polynomial_quotient_hom_eq_of_coordinates J
    intro j
    exact (congrFun hpoint j).symm.trans (congrFun hx.2 j)
  subst q0
  letI : (RingHom.ker q.toRingHom).IsPrime := RingHom.ker_isPrime _
  exact localized_annihilator_generator_at_equal_primes (Ideal.Quotient.mk J Θ)
    (RingHom.ker q.toRingHom) L hq hAnn

end LinearStudy
