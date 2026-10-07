module
public import Linear.ProjectiveAffineSmoothPoint
public import Linear.SmoothPointPrincipalOpen
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- A nonzero regular function on the inhabited actual affine projective
chart can be avoided by an actual smooth complex point. -/
theorem IntegralProjectiveEquations.exists_smooth_affine_point_avoiding
    (V : IntegralProjectiveEquations n) (x0 : Fin n → ℂ)
    (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet)
    (H : MvPolynomial (Fin n) ℂ) (hH : H ∉ V.affineIdeal) :
    ∃ (x : Fin n → ℂ) (hx : normalizedProjectivePoint x ∈ V.zeroSet),
      MvPolynomial.eval x H ≠ 0 ∧
      Algebra.IsSmoothAt ℂ (V.affinePoint x hx).asIdeal := by
  letI : V.affineIdeal.IsPrime := V.affineIdeal_isPrime_of_point x0 hx0
  let A := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  letI : Algebra.FinitePresentation ℂ A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let a : A := Ideal.Quotient.mk V.affineIdeal H
  have ha : a ≠ 0 := fun h => hH (Ideal.Quotient.eq_zero_iff_mem.mp h)
  obtain ⟨ρ, hρ, hs⟩ := domain_exists_smooth_rational_point_avoiding (K := ℂ) (A := A) a ha
  obtain ⟨x, hx, hp⟩ := V.affineAlgHom_point ρ
  refine ⟨x, hx, ?_, ?_⟩
  · have hk : RingHom.ker (MvPolynomial.aeval (R := ℂ) x).toRingHom =
        (RingHom.ker ρ.toRingHom).comap (Ideal.Quotient.mk V.affineIdeal) :=
      (V.affinePointIdeal_comap x hx).symm.trans
        (congrArg (fun J => J.comap (Ideal.Quotient.mk V.affineIdeal)) hp)
    intro hz
    have hm : H ∈ RingHom.ker (MvPolynomial.aeval (R := ℂ) x).toRingHom := by
      change MvPolynomial.eval x H = 0
      exact hz
    rw [hk] at hm
    exact hρ hm
  · have he : V.affinePoint x hx = rationalPointPrime ρ := PrimeSpectrum.ext hp
    change V.affinePoint x hx ∈ Algebra.smoothLocus ℂ A
    rw [he]
    exact hs

end LinearStudy
