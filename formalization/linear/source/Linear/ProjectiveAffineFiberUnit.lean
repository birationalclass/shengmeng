module
public import Linear.ProjectiveAffineFiberFinite
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K σ : Type*} [Field K] [IsAlgClosed K] [Finite σ]

/-- Nonvanishing at every actual closed point makes a polynomial a unit
in the original scheme quotient, including its possible nilpotents. -/
theorem polynomialQuotient_isUnit_of_nonvanishing
    (I : Ideal (MvPolynomial σ K)) (p : MvPolynomial σ K)
    (hp : ∀ x ∈ MvPolynomial.zeroLocus K I, MvPolynomial.eval x p ≠ 0) :
    IsUnit (Ideal.Quotient.mk I p) := by
  let J := I ⊔ Ideal.span {p}
  have hJ : MvPolynomial.zeroLocus K J = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxI : x ∈ MvPolynomial.zeroLocus K I := fun H hH =>
      hx H (Ideal.mem_sup_left hH)
    apply hp x hxI
    exact hx p (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton p)))
  have ht : J = ⊤ := by
    apply Ideal.radical_eq_top.mp
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K) J, hJ]
    ext H
    simp [MvPolynomial.vanishingIdeal]
  have hone : (1 : MvPolynomial σ K) ∈ I ⊔ Ideal.span {p} := by
    change (1 : MvPolynomial σ K) ∈ J
    rw [ht]
    trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hone
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hb
  have he := congrArg (Ideal.Quotient.mk I) hab
  rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add, hc, map_mul, map_one] at he
  exact IsUnit.of_mul_eq_one _ he

/-- The original homogeneous coordinate denominator is an ACTUAL unit in
the affine projective fiber quotient, derived from no base point. -/
theorem projectiveAffineFiberQuotient_denominator_isUnit
    {n : ℕ} (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (y : Fin n → ℂ) :
    IsUnit (Ideal.Quotient.mk (projectiveAffineFiberIdeal f V y)
      (affineChartPolynomialMap (f.forms 0))) := by
  apply polynomialQuotient_isUnit_of_nonvanishing
  intro z hz
  exact (projectiveAffineFiberIdeal_point f V y z hz).2.1

end LinearStudy
