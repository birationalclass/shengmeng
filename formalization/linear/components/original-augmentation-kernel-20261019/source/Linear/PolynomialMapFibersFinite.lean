module
public import Linear.HomogeneousMapFinite
public import Linear.FiniteRationalPoints
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

/-- An actually finite polynomial map has finite-dimensional actual
K-rational fiber algebras. The quotient equations are P_i-w_i. -/
theorem polynomialMap_fiber_quotient_finite
    {K ι κ : Type*} [Field K]
    (P : κ → MvPolynomial ι K)
    (hP : ((MvPolynomial.aeval P : MvPolynomial κ K →ₐ[K]
      MvPolynomial ι K).toRingHom).Finite) (w : κ → K) :
    Module.Finite K (MvPolynomial ι K ⧸
      Ideal.span (Set.range (fun i => P i - MvPolynomial.C (w i)))) := by
  let I := Ideal.span (Set.range (fun i => P i - MvPolynomial.C (w i)))
  let Q := MvPolynomial ι K ⧸ I
  let π := Ideal.Quotient.mkₐ K I
  let φ : MvPolynomial κ K →ₐ[K] MvPolynomial ι K := MvPolynomial.aeval P
  let e : MvPolynomial κ K →ₐ[K] K := MvPolynomial.aeval w
  let c : K →ₐ[K] Q := Algebra.ofId K Q
  have hφX : ∀ i, φ (MvPolynomial.X i) = P i := fun i => MvPolynomial.aeval_X P i
  have heX : ∀ i, e (MvPolynomial.X i) = w i := fun i => MvPolynomial.aeval_X w i
  have hcC : ∀ a : K, c a = π (MvPolynomial.C a) := fun a => rfl
  have hπ : π.toRingHom.Finite :=
    RingHom.Finite.of_surjective π.toRingHom Ideal.Quotient.mk_surjective
  have hc := hπ.comp hP
  have he : π.comp φ = c.comp e := by
    apply MvPolynomial.algHom_ext
    intro i
    change π (φ (MvPolynomial.X i)) = c (e (MvPolynomial.X i))
    rw [hφX, heX, hcC]
    exact Ideal.Quotient.eq.mpr (Ideal.subset_span (Set.mem_range_self i))
  have her : π.toRingHom.comp φ.toRingHom =
      (algebraMap K Q).comp (MvPolynomial.aeval w).toRingHom :=
    congrArg AlgHom.toRingHom he
  rw [her] at hc
  exact RingHom.finite_algebraMap.mp (RingHom.Finite.of_comp_finite hc)

/-- Finiteness of the actual polynomial map implies finiteness of every
actual rational vector fiber, with no regularity or smoothness assumption. -/
theorem polynomialMap_fibers_finite
    {K ι κ : Type*} [Field K]
    (P : κ → MvPolynomial ι K)
    (hP : ((MvPolynomial.aeval P : MvPolynomial κ K →ₐ[K]
      MvPolynomial ι K).toRingHom).Finite) (w : κ → K) :
    {v : ι → K | (fun i => MvPolynomial.eval v (P i)) = w}.Finite := by
  let I := Ideal.span (Set.range (fun i => P i - MvPolynomial.C (w i)))
  let : Module.Finite K (MvPolynomial ι K ⧸ I) :=
    polynomialMap_fiber_quotient_finite P hP w
  have hz := polynomial_zeroLocus_finite_of_module_finite I
  have he : {v : ι → K | (fun i => MvPolynomial.eval v (P i)) = w} =
      MvPolynomial.zeroLocus K I := by
    rw [MvPolynomial.zeroLocus_span]
    ext v
    simp only [Set.mem_ofPred_eq, Set.forall_mem_range, map_sub, MvPolynomial.aeval_C,
      Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero, funext_iff]
    rfl
  rwa [← he] at hz

end LinearStudy
