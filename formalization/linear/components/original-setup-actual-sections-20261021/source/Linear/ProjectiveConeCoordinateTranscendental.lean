module
public import Linear.ScalingOrbitTranscendental
public import Linear.ProjectiveScalingFixedRatios
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- The ORIGINAL nonzero cone coordinate is transcendental over the
ORIGINAL projective coordinate-ratio field. Actual scaling maps provide
the infinite orbit; transcendence is not an input hypothesis. -/
theorem projectiveConeFractionCoordinates_zero_transcendental
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    Transcendental (projectiveCoordinateRatioField V)
      (projectiveConeFractionCoordinates V 0) := by
  letI := V.prime
  let u : ℕ → ℂˣ := fun N => Units.mk0 ((N + 1 : ℕ) : ℂ)
    (by exact_mod_cast Nat.succ_ne_zero N)
  apply transcendental_of_scaling_orbit (projectiveCoordinateRatioField V)
    (projectiveConeFractionCoordinates V 0)
    (projectiveConeFractionCoordinates_zero_ne_zero V x hx)
    (fun N => projectiveConeScalingMap V (u N))
  · intro N a ha
    exact projectiveConeScalingMap_fixes_ratioField V (u N) x hx a ha
  · intro N
    simpa only [u, Units.val_mk0] using projectiveConeScalingMap_coordinate V (u N) 0

end LinearStudy
