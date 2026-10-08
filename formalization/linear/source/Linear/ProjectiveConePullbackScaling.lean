module
public import Linear.ProjectiveConeRatioRatFunc
public import Linear.ProjectiveChartMapCoordinates
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- The actual cone pullback of the scaling coordinate equals a coefficient
in the actual projective field times its q-th power. -/
theorem projectiveConePullback_exists_scaling_coefficient
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    ∃ u : projectiveCoordinateRatioField V, u ≠ 0 ∧
      projectiveCoordinateFractionMap f V hq hf hV (projectiveConeFractionCoordinates V 0) =
        algebraMap (projectiveCoordinateRatioField V)
          (FractionRing (CoordinateRing n ⧸ V.ideal.toIdeal)) u *
            projectiveConeFractionCoordinates V 0 ^ f.degree := by
  letI := V.prime
  let z := projectiveConeFractionCoordinates V
  let u : projectiveCoordinateRatioField V :=
    ⟨coordinateRatioPolynomialMap z (affineChartPolynomialMap (f.forms 0)),
      coordinateRatioPolynomialMap_mem z _⟩
  have hz := projectiveConeFractionCoordinates_zero_ne_zero V x hx
  have he : projectiveCoordinateFractionMap f V hq hf hV (z 0) =
      (u : FractionRing (CoordinateRing n ⧸ V.ideal.toIdeal)) * z 0 ^ f.degree := by
    rw [projectiveCoordinateFractionMap_coordinate]
    change MvPolynomial.aeval z (f.forms 0) =
      coordinateRatioPolynomialMap z (affineChartPolynomialMap (f.forms 0)) * z 0 ^ f.degree
    rw [coordinateRatioPolynomialMap_homogeneous z hz _ (f.homogeneous 0)]
    rw [mul_comm ((z 0)⁻¹ ^ f.degree), mul_assoc, ← mul_pow,
      inv_mul_cancel₀ (show z 0 ≠ 0 from hz), one_pow, mul_one]
  have hn : u ≠ 0 := by
    intro h
    have h0 : projectiveCoordinateFractionMap f V hq hf hV (z 0) = 0 := by
      rw [he, h]
      simp
    exact hz ((projectiveCoordinateFractionMap f V hq hf hV).injective (by simpa using h0))
  exact ⟨u, hn, he⟩

end LinearStudy
