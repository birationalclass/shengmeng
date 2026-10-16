module
public import Linear.ProjectiveAffineSmoothPoint
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

/-- Equality of rational point kernels over the fixed base field determines
the actual coordinate values, not merely the underlying prime. -/
theorem polynomial_algHom_eq_of_point_kernel
    {K σ : Type*} [Field K]
    (ρ : MvPolynomial σ K →ₐ[K] K) (x : σ → K)
    (h : RingHom.ker ρ.toRingHom = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom) :
    ρ = MvPolynomial.aeval x := by
  apply MvPolynomial.algHom_ext
  intro i
  have hh : MvPolynomial.X i - MvPolynomial.C (x i) ∈
      RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom := by
    simp
  rw [← h, RingHom.mem_ker] at hh
  change ρ (MvPolynomial.X i - MvPolynomial.C (x i)) = 0 at hh
  have hc : ρ (MvPolynomial.C (x i)) = x i := ρ.commutes (x i)
  rw [map_sub, hc, sub_eq_zero] at hh
  simpa only [MvPolynomial.aeval_X] using hh

theorem IntegralProjectiveEquations.affineAlgHom_point_evaluation
    {n : ℕ} (V : IntegralProjectiveEquations n)
    (ρ : (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) →ₐ[ℂ] ℂ) :
    ∃ (x : Fin n → ℂ) (hx : normalizedProjectivePoint x ∈ V.zeroSet),
      V.affinePointIdeal x = RingHom.ker ρ.toRingHom ∧
      ρ.comp (Ideal.Quotient.mkₐ ℂ V.affineIdeal) = MvPolynomial.aeval x := by
  obtain ⟨x, hx, hp⟩ := V.affineAlgHom_point ρ
  refine ⟨x, hx, hp, ?_⟩
  apply polynomial_algHom_eq_of_point_kernel
  change RingHom.ker (ρ.toRingHom.comp (Ideal.Quotient.mk V.affineIdeal)) = _
  rw [← RingHom.comap_ker, ← hp, V.affinePointIdeal_comap x hx]

end LinearStudy
