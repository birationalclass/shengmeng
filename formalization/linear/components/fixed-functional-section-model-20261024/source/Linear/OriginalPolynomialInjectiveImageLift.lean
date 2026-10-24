module
public import Linear.OriginalProjectivePolynomialSection
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
/-- Pure ORIGINAL quotient polynomial lifting for one nonzero image of
an injective linear map. It keeps Q in the original coordinate ring and
proves nonmembership in the original ideal. No sheaf is an input. -/
theorem originalPolynomial_exists_of_injective_image
    {n : ℕ} (V : IntegralProjectiveEquations n)
    {D : Type} [AddCommGroup D] [Module (CoordinateRing n ⧸ V.ideal.toIdeal) D]
    (e : D →ₗ[CoordinateRing n ⧸ V.ideal.toIdeal] (CoordinateRing n ⧸ V.ideal.toIdeal))
    (he : Function.Injective e) (m : ℕ) (z : D) (hne : z ≠ 0)
    (himage : e z ∈ homogeneousQuotientPiece V.ideal.toIdeal m) :
    ∃ Q : CoordinateRing n,Q.IsHomogeneous m ∧ Q ∉ V.ideal.toIdeal ∧
      Ideal.Quotient.mk V.ideal.toIdeal Q=e z := by
  obtain ⟨Q,hQ,hval⟩ := (homogeneousQuotientPiece_mem_iff V.ideal.toIdeal m (e z)).mp himage
  refine ⟨Q,hQ,?_,hval⟩
  intro hmem
  apply hne
  apply he
  rw [map_zero,← hval]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
end LinearStudy
