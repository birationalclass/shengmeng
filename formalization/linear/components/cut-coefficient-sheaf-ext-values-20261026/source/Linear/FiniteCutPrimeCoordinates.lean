module
public import Linear.FiniteReducedLocalCut
public import Linear.FiniteRationalPoints
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy

/-- Every prime of the actual zero-dimensional cut is an actual coordinate
point. This follows from its original Artinian quotient and Nullstellensatz,
not an assumed identification of primes with a chosen point set. -/
theorem artinian_polynomial_cut_prime_has_coordinates
    {K ι : Type*} [Field K] [IsAlgClosed K] [Finite ι]
    (I P : Ideal (MvPolynomial ι K)) [P.IsPrime]
    [IsArtinianRing (MvPolynomial ι K ⧸ I)] (hIP : I ≤ P) :
    ∃ x : ι → K,x ∈ MvPolynomial.zeroLocus K I ∧
      P=RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom := by
  let p := P.map (Ideal.Quotient.mk I)
  letI : p.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by simpa only [Ideal.mk_ker] using hIP)
  have hcomap : p.comap (Ideal.Quotient.mk I)=P := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot,Ideal.mk_ker]
    exact sup_eq_left.mpr hIP
  have hmax : P.IsMaximal := by
    rw [← hcomap]
    exact Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      (K := p) (H := IsArtinianRing.isMaximal_of_isPrime p)
  obtain ⟨x,hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hmax
  have hk : P=RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom := by
    rw [hx]
    ext F
    exact MvPolynomial.mem_vanishingIdeal_singleton_iff x F
  refine ⟨x,?_,hk⟩
  intro F hF
  have h := hIP hF
  rw [hk] at h
  exact h

end LinearStudy
