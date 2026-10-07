module
public import Linear.ProjectiveAffineSmoothLocus
public import Linear.SmoothRationalPoint
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

theorem IntegralProjectiveEquations.affineAlgHom_point
    (V : IntegralProjectiveEquations n)
    (ρ : (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) →ₐ[ℂ] ℂ) :
    ∃ (x : Fin n → ℂ) (hx : normalizedProjectivePoint x ∈ V.zeroSet),
      V.affinePointIdeal x = RingHom.ker ρ.toRingHom := by
  let x := fun i => ρ (Ideal.Quotient.mk V.affineIdeal (MvPolynomial.X i))
  have hcomp : ρ.comp (Ideal.Quotient.mkₐ ℂ V.affineIdeal) =
      MvPolynomial.aeval (R := ℂ) x := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [x]
  have hI : V.affineIdeal ≤ RingHom.ker (MvPolynomial.aeval (R := ℂ) x).toRingHom := by
    intro H hH
    change MvPolynomial.aeval (R := ℂ) x H = 0
    rw [← hcomp]
    change ρ (Ideal.Quotient.mk V.affineIdeal H) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hH, map_zero]
  have hx : normalizedProjectivePoint x ∈ V.zeroSet := by
    apply (V.normalizedPoint_mem_iff x).mpr
    have h := Ideal.map_le_iff_le_comap.mp hI
    rw [affineChartPolynomialMap_pointKernel_comap] at h
    exact h
  refine ⟨x, hx, ?_⟩
  apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk V.affineIdeal)
    Ideal.Quotient.mk_surjective
  rw [V.affinePointIdeal_comap x hx, RingHom.comap_ker]
  exact congrArg (fun φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ => RingHom.ker φ.toRingHom)
    hcomp.symm

/-- Every inhabited standard affine chart of the original integral
projective variety has an actual smooth complex point. -/
theorem IntegralProjectiveEquations.exists_smooth_affine_point
    (V : IntegralProjectiveEquations n) (x0 : Fin n → ℂ)
    (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ (x : Fin n → ℂ) (hx : normalizedProjectivePoint x ∈ V.zeroSet),
      Algebra.IsSmoothAt ℂ (V.affinePoint x hx).asIdeal := by
  letI : V.affineIdeal.IsPrime := V.affineIdeal_isPrime_of_point x0 hx0
  let A := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  letI : Algebra.FinitePresentation ℂ A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨a, ρ, _, _, hs⟩ := domain_exists_smooth_rational_point (K := ℂ) (A := A)
  obtain ⟨x, hx, hp⟩ := V.affineAlgHom_point ρ
  refine ⟨x, hx, ?_⟩
  have he : V.affinePoint x hx = rationalPointPrime ρ := PrimeSpectrum.ext hp
  change V.affinePoint x hx ∈ Algebra.smoothLocus ℂ A
  rw [he]
  exact hs

end LinearStudy
