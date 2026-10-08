module
public import Linear.ProjectiveScalingMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- Every actual projective coordinate ratio is fixed by cone scaling. -/
theorem projectiveConeScalingMap_ratio
    (V : IntegralProjectiveEquations n) (u : ℂˣ)
    (x : Fin n → ℂ) (hx : normalizedProjectivePoint x ∈ V.zeroSet) (i : Fin n) :
    letI := V.prime
    projectiveConeScalingMap V u
      (projectiveConeFractionCoordinates V i.succ / projectiveConeFractionCoordinates V 0) =
      projectiveConeFractionCoordinates V i.succ / projectiveConeFractionCoordinates V 0 := by
  letI := V.prime
  rw [map_div₀, projectiveConeScalingMap_coordinate, projectiveConeScalingMap_coordinate]
  have hu : algebraMap ℂ (FractionRing (CoordinateRing n ⧸ V.ideal.toIdeal)) (u : ℂ) ≠ 0 := by
    simpa only [map_zero] using
      (algebraMap ℂ (FractionRing (CoordinateRing n ⧸ V.ideal.toIdeal))).injective.ne (Units.ne_zero u)
  exact mul_div_mul_left _ _ hu

/-- Scaling fixes the WHOLE actual coordinate-ratio field, not only
the displayed generators. -/
theorem projectiveConeScalingMap_fixes_ratioField
    (V : IntegralProjectiveEquations n) (u : ℂˣ)
    (x : Fin n → ℂ) (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    ∀ a ∈ projectiveCoordinateRatioField V, projectiveConeScalingMap V u a = a := by
  letI := V.prime
  intro a ha
  change a ∈ IntermediateField.adjoin ℂ
    (Set.range (fun i : Fin n => projectiveConeFractionCoordinates V i.succ /
      projectiveConeFractionCoordinates V 0)) at ha
  induction ha using IntermediateField.adjoin_induction with
  | mem a ha =>
    obtain ⟨i, rfl⟩ := ha
    exact projectiveConeScalingMap_ratio V u x hx i
  | algebraMap a => exact (projectiveConeScalingMap V u).commutes a
  | add a b ha hb h1 h2 => rw [map_add, h1, h2]
  | inv a ha h1 => rw [map_inv₀, h1]
  | mul a b ha hb h1 h2 => rw [map_mul, h1, h2]

end LinearStudy
