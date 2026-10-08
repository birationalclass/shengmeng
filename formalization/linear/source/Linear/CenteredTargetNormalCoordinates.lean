module
public import Linear.ProjectiveTargetNormalCoordinates
public import Linear.LocalGeneratorsEquiv
public import Linear.PolynomialLocalParameters
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace LinearStudy
variable {K σ ι : Type*} [Field K] [Finite σ]

/-- Actual local generators vanishing at the point imply containment of the
original ideal in the point kernel; this containment is not a new assumption. -/
theorem polynomial_local_generators_imply_point_containment
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime] (z : σ → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) z).toRingHom)
    (H : ι → MvPolynomial σ K)
    (hlocal : I.map (algebraMap _ (Localization.AtPrime P)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (H i))))
    (h0 : ∀ i, MvPolynomial.eval z (H i) = 0) : I ≤ P := by
  have hformal := formalPolynomialIdeal_local_generators I P z hP H hlocal
  have hle : I.map (formalPolynomialAtPoint z) ≤
      RingHom.ker (MvPowerSeries.constantCoeff (σ := σ) (R := K)) := by
    rw [hformal]
    apply Ideal.span_le.mpr
    rintro F ⟨i, rfl⟩
    change (formalPolynomialAtPoint z (H i)).constantCoeff = 0
    rw [formalPolynomialAtPoint_constantCoeff, h0]
  intro F hF
  have hh := hle (Ideal.mem_map_of_mem (formalPolynomialAtPoint z) hF)
  rw [hP]
  change MvPolynomial.eval z F = 0
  exact (formalPolynomialAtPoint_constantCoeff z F).symm.trans hh

/-- Recenter the SAME actual target ideal and generators at the origin. -/
theorem polynomial_local_generators_actual_centering
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime] (z : σ → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) z).toRingHom)
    (H : ι → MvPolynomial σ K)
    (hlocal : I.map (algebraMap _ (Localization.AtPrime P)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (H i))))
    (h0 : ∀ i, MvPolynomial.eval z (H i) = 0) :
    let E := polynomialTranslation z
    let Q := RingHom.ker (MvPolynomial.aeval (R := K) (0 : σ → K)).toRingHom
    letI : Q.IsPrime := RingHom.ker_isPrime _
    (I.map E.toRingHom) ≤ Q ∧
    (∀ i, MvPolynomial.eval (0 : σ → K) (E (H i)) = 0) ∧
    (I.map E.toRingHom).map (algebraMap _ (Localization.AtPrime Q)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime Q) (E (H i)))) := by
  intro E Q
  letI : Q.IsPrime := RingHom.ker_isPrime _
  have hp : P = Q.comap E.toRingHom := by
    rw [hP]
    ext F
    change MvPolynomial.eval z F = 0 ↔ MvPolynomial.eval (0 : σ → K) (E F) = 0
    simp only [E, polynomialTranslation_evaluation, Pi.zero_apply, zero_add]
  have hIP := polynomial_local_generators_imply_point_containment I P z hP H hlocal h0
  refine ⟨?_, ?_, ?_⟩
  · apply Ideal.map_le_iff_le_comap.mpr
    rw [← hp]
    exact hIP
  · intro i
    simpa only [E, polynomialTranslation_evaluation, Pi.zero_apply, zero_add] using h0 i
  · exact local_ideal_generators_under_ringEquiv I P Q E.toRingEquiv hp H hlocal

theorem polynomial_normal_firstJet_actual_centering
    {α β : Type*} [Finite α] [Finite β] [DecidableEq α] [DecidableEq β]
    (z : α ⊕ β → K) (H : β → MvPolynomial (α ⊕ β) K)
    (hD : ∀ i j, MvPolynomial.eval z (MvPolynomial.pderiv j (H i)) =
      if j = Sum.inr i then 1 else 0) :
    ∀ i j, MvPolynomial.eval (0 : α ⊕ β → K)
      (MvPolynomial.pderiv j (polynomialTranslation z (H i))) =
        if j = Sum.inr i then 1 else 0 := by
  intro i j
  rw [polynomialTranslation_pderiv, polynomialTranslation_evaluation]
  simpa only [Pi.zero_apply, zero_add] using hD i j

end LinearStudy
