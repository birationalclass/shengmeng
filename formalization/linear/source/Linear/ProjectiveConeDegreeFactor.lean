module
public import Linear.FieldEndomorphismRationalDegree
public import Linear.ScaledPowerTranscendental
public import Linear.ProjectiveConePullbackScaling
public import Linear.RatFuncScaledPowerDegree
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- For the ORIGINAL f,V, the WHOLE cone image-field degree is q times
the WHOLE projective coordinate-ratio image-field degree. -/
theorem projectiveConeFractionField_degree_factor
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    let A := CoordinateRing n ⧸ V.ideal.toIdeal
    let E := projectiveCoordinateRatioField V
    let γ := projectiveCoordinateFractionMap f V hq hf hV
    let σ := projectiveCoordinateRatioMap f V hq hf hV x hx
    Module.finrank γ.fieldRange (FractionRing A) =
      f.degree * Module.finrank σ.fieldRange E := by
  letI := V.prime
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  let F := FractionRing A
  let E := projectiveCoordinateRatioField V
  let γ := projectiveCoordinateFractionMap f V hq hf hV
  let σ := projectiveCoordinateRatioMap f V hq hf hV x hx
  let t := projectiveConeFractionCoordinates V 0
  letI : Algebra.EssFiniteType ℂ E := coordinateRatioField_essFiniteType _
  letI : Module.Finite σ.fieldRange E := fieldEndomorphism_range_finite σ
  obtain ⟨u, hu, he⟩ := projectiveConePullback_exists_scaling_coefficient f V hq hf hV x hx
  have hc : ∀ a : E, γ (a : F) = (σ a : F) := by intro a; rfl
  have ht : Transcendental E (γ t) := by
    rw [he]
    exact transcendental_scaled_power t
      (projectiveConeFractionCoordinates_zero_transcendental V x hx) u hu f.degree hq
  have hvar : Module.finrank (IntermediateField.adjoin E {γ t}) F = f.degree := by
    rw [he]
    have h := rationalField_scaled_power_finrank (projectiveConeRatioRatFuncEquiv V x hx)
      u hu f.degree
    rw [projectiveConeRatioRatFuncEquiv_X] at h
    exact h
  have h := fieldEndomorphism_rational_degree_factor E γ σ hc t
    (projectiveConeRatioField_adjoin_coordinate_top V x hx) ht
  rw [hvar] at h
  exact h

end LinearStudy
