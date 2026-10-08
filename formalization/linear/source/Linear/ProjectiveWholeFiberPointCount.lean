module
public import Linear.ProjectiveAffineFiberPointEquiv
public import Linear.PolynomialReducedPointCount
public import Linear.ProjectiveWholeReducedFiber
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {n : ℕ}

/-- For an entire fiber contained in the source chart, reducedness gives
its ACTUAL point count as the dimension of its ACTUAL fiber-equation quotient.
The separate q^r degree identity is not built into the hypotheses. -/
theorem projectiveWholeFiber_card_eq_affine_quotient_finrank
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (y : Fin n → ℂ)
    (hy : normalizedProjectivePoint y ∈ V.zeroSet)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (hchart : ∀ (v : CoordinateVector n) (hv : v ≠ 0),
      f.onPoints (Projectivization.mk ℂ v hv) = normalizedProjectivePoint y → v 0 ≠ 0)
    [Module.Finite ℂ (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineFiberIdeal f V y)]
    [IsReduced (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineFiberIdeal f V y)] :
    Nat.card (f.onPoints ⁻¹' {normalizedProjectivePoint y}) =
      Module.finrank ℂ (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineFiberIdeal f V y) := by
  obtain ⟨e⟩ := projectiveAffineFiber_nonempty_whole_point_equiv f V y hy hV hchart
  exact (Nat.card_congr e).symm.trans (polynomialZeroLocus_card_eq_finrank _)

/-- Construct the entire finite fiber and its reduced finite-dimensional
equation quotient from original f,V, then prove their exact point/dimension
identity. Neither reducedness nor the point count is an input. -/
theorem projective_exists_whole_reduced_fiber_point_count
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x0 : Fin n → ℂ)
    (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ (y : Fin n → ℂ), normalizedProjectivePoint y ∈ V.zeroSet ∧
      (f.onPoints ⁻¹' {normalizedProjectivePoint y}).Finite ∧
      (∀ (v : CoordinateVector n) (hv : v ≠ 0),
        f.onPoints (Projectivization.mk ℂ v hv) = normalizedProjectivePoint y → v 0 ≠ 0) ∧
      Module.Finite ℂ (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineFiberIdeal f V y) ∧
      IsReduced (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineFiberIdeal f V y) ∧
      Nat.card (f.onPoints ⁻¹' {normalizedProjectivePoint y}) =
        Module.finrank ℂ (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineFiberIdeal f V y) := by
  obtain ⟨y, hy, hfiber, hchart, hfinite, hred⟩ :=
    projective_exists_whole_reduced_fiber f V hq hf hV x0 hx0
  letI := hfinite
  letI := hred
  exact ⟨y, hy, hfiber, hchart, hfinite, hred,
    projectiveWholeFiber_card_eq_affine_quotient_finrank f V y hy hV hchart⟩

end LinearStudy
