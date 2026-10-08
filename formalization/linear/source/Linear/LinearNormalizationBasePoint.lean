module
public import Linear.HomogeneousLinearNormalization
public import Mathlib.Algebra.Polynomial.Eval.Coeff
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type*} [Field K] [Infinite K] {n s : ℕ}

omit [Infinite K] in
theorem homogeneous_zeroLocus_smul
    (I : Ideal (MvPolynomial (Fin n) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ _))
    (v : Fin n → K) (hv : v ∈ MvPolynomial.zeroLocus K I) (a : K) :
    a • v ∈ MvPolynomial.zeroLocus K I := by
  intro P hP
  rw [← MvPolynomial.sum_homogeneousComponent P,map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [MvPolynomial.aeval_eq_eval]
  rw [homogeneous_eval_smul (MvPolynomial.homogeneousComponent_isHomogeneous j P)]
  have hc : MvPolynomial.eval v (MvPolynomial.homogeneousComponent j P) = 0 := by
    simpa only [MvPolynomial.aeval_eq_eval] using
      hv _ (MvPolynomial.homogeneousComponent_mem_of_mem hI hP j)
  rw [hc,mul_zero]

/-- The ACTUAL integral linear normalization has no nonzero common
zero on the original homogeneous cone. An integral equation evaluated
on every scalar multiple rules out a nonzero base point. -/
theorem integral_linear_normalization_origin_zeroLocus
    (I : Ideal (MvPolynomial (Fin n) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ _))
    (L : Fin s → MvPolynomial (Fin n) K) (hL : ∀ i, (L i).IsHomogeneous 1)
    (g : MvPolynomial (Fin s) K →ₐ[K] (MvPolynomial (Fin n) K ⧸ I))
    (hg : ∀ i, g (MvPolynomial.X i) = Ideal.Quotient.mk I (L i))
    (hint : g.IsIntegral) (v : Fin n → K)
    (hv : v ∈ MvPolynomial.zeroLocus K I) (hLv : ∀ i, MvPolynomial.eval v (L i) = 0) :
    v = 0 := by
  classical
  let φ (a : K) : (MvPolynomial (Fin n) K ⧸ I) →ₐ[K] K :=
    Ideal.Quotient.liftₐ I (MvPolynomial.aeval (a • v))
      (homogeneous_zeroLocus_smul I hI v hv a)
  have hφ (a : K) : (φ a).comp g = MvPolynomial.aeval (0 : Fin s → K) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply,hg]
    simp only [φ,Ideal.Quotient.liftₐ_apply,Ideal.Quotient.lift_mk,
      AlgHom.coe_toRingHom,MvPolynomial.aeval_X,MvPolynomial.aeval_eq_eval,Pi.zero_apply]
    rw [homogeneous_eval_smul (hL i),hLv i,mul_zero]
  ext i
  by_contra hvi
  have hvi0 : v i ≠ 0 := by simpa using hvi
  obtain ⟨p,hp,hroot⟩ := hint (Ideal.Quotient.mk I (MvPolynomial.X i))
  let e : MvPolynomial (Fin s) K →+* K := (MvPolynomial.aeval (0 : Fin s → K)).toRingHom
  let p0 := p.map e
  have hp0 : p0.Monic := hp.map e
  have hzero (a : K) : p0.eval (a * v i) = 0 := by
    have h := congrArg (φ a).toRingHom hroot
    rw [map_zero,Polynomial.hom_eval₂] at h
    have he : (φ a).toRingHom.comp g.toRingHom = e := by
      exact congrArg AlgHom.toRingHom (hφ a)
    rw [he] at h
    have hφX : (φ a).toRingHom (Ideal.Quotient.mk I (MvPolynomial.X i)) = a*v i := by
      change (φ a) (Ideal.Quotient.mk I (MvPolynomial.X i)) = a*v i
      simp only [φ,Ideal.Quotient.liftₐ_apply,
        Ideal.Quotient.lift_mk,AlgHom.coe_toRingHom,MvPolynomial.aeval_X,
        Pi.smul_apply,smul_eq_mul]
    rw [hφX] at h
    change p.eval₂ e (a*v i) = 0 at h
    simpa only [p0,Polynomial.eval_map] using h
  have hall (b : K) : p0.eval b = 0 := by
    have h := hzero (b/v i)
    simpa only [div_mul_cancel₀ b hvi0] using h
  exact hp0.ne_zero (Polynomial.zero_of_eval_zero p0 hall)

end LinearStudy
