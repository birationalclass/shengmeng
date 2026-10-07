module
public import Linear.TargetLinearNormal
public import Linear.LocalGeneratorsEquiv
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open scoped Matrix

/-- The first-order-normal generators generate the completed image of the
ORIGINAL ideal under the constructed actual ambient linear coordinates. -/
theorem original_local_ideal_firstOrder_normal_form
    {K α β : Type*} [Field K] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Nonempty β]
    (I : Ideal (MvPolynomial (α ⊕ β) K)) (x : α ⊕ β → K)
    (G : β → MvPolynomial (α ⊕ β) K)
    (hs : letI : (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom).IsPrime :=
        RingHom.ker_isPrime _
      I.map (algebraMap _ (Localization.AtPrime
          (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom))) =
        Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime
          (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)) (G i))))
    (h0 : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j =>
      MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i))))) :
    ∃ (M : Matrix (α ⊕ β) (α ⊕ β) K) (hM : Matrix.det M ≠ 0)
      (H : β → MvPowerSeries (α ⊕ β) K),
      (∀ i, H i - MvPowerSeries.X (Sum.inr i) ∈
        (IsLocalRing.maximalIdeal (MvPowerSeries (α ⊕ β) K)) ^ 2) ∧
      I.map ((formalPolynomialAtPoint (M⁻¹ *ᵥ x)).comp
        (polynomialLinearChangeEquiv M hM).toRingHom) = Ideal.span (Set.range H) := by
  classical
  obtain ⟨M, hM, H, hfirst, hideal⟩ :=
    polynomial_equations_formal_firstOrder_normal_form G x h0 hJ
  refine ⟨M, hM, H, hfirst, ?_⟩
  let C := polynomialLinearChangeEquiv M hM
  let y := M⁻¹ *ᵥ x
  let Q := RingHom.ker (MvPolynomial.aeval (R := K) y).toRingHom
  let : Q.IsPrime := RingHom.ker_isPrime _
  have hs' := polynomial_local_generators_under_linear_change I x M hM G hs
  have hf := formalPolynomialIdeal_local_generators (I.map C.toRingHom) Q y rfl
    (fun i => C (G i)) hs'
  rw [Ideal.map_map] at hf
  exact hf.trans hideal.symm
end LinearStudy
