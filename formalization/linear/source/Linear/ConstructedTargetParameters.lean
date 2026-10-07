module
public import Linear.OriginalPolynomialNormal
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open scoped Matrix

/-- The actual coordinate shear and normal polynomial generators construct
the target parameters; their spanning condition is no longer an assumption. -/
theorem constructed_normal_target_tangent_parameters
    {K α β : Type*} [Field K] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (I : Ideal (MvPolynomial (α ⊕ β) K)) (x : α ⊕ β → K)
    (hIP : I ≤ RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
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
    ∃ (M : Matrix (α ⊕ β) (α ⊕ β) K) (hM : Matrix.det M ≠ 0),
      let Q := RingHom.ker (MvPolynomial.aeval (R := K) (M⁻¹ *ᵥ x)).toRingHom
      letI : Q.IsPrime := RingHom.ker_isPrime _
      let I' := I.map (polynomialLinearChangeEquiv M hM).toRingHom
      ∃ hIQ : I' ≤ Q,
      let J := I'.map (algebraMap _ (Localization.AtPrime Q))
      letI : Nontrivial (Localization.AtPrime Q ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
        (polynomial_local_ideal_ne_top I' Q hIQ)
      letI : IsLocalRing (Localization.AtPrime Q ⧸ J) := IsLocalRing.of_surjective'
        (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
      Ideal.span (Set.range (fun i : α => Ideal.Quotient.mk J
        (algebraMap (MvPolynomial (α ⊕ β) K) (Localization.AtPrime Q)
          (MvPolynomial.X (Sum.inl i) - MvPolynomial.C ((M⁻¹ *ᵥ x) (Sum.inl i)))))) =
        IsLocalRing.maximalIdeal (Localization.AtPrime Q ⧸ J) := by
  classical
  obtain ⟨M, hM, H, h0H, hDH, hlocal⟩ :=
    original_local_ideal_normal_polynomial_generators I x G hs h0 hJ
  refine ⟨M, hM, ?_⟩
  let Q := RingHom.ker (MvPolynomial.aeval (R := K) (M⁻¹ *ᵥ x)).toRingHom
  let : Q.IsPrime := RingHom.ker_isPrime _
  let I' := I.map (polynomialLinearChangeEquiv M hM).toRingHom
  have hIQ : I' ≤ Q := by
    apply Ideal.map_le_iff_le_comap.mpr
    rw [← point_kernel_under_polynomialLinearChange M hM x]
    exact hIP
  refine ⟨hIQ, ?_⟩
  exact polynomial_firstOrder_tangents_generate_local_quotient I' Q hIQ (M⁻¹ *ᵥ x)
    rfl H hlocal h0H hDH
end LinearStudy
