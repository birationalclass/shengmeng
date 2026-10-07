module
public import Linear.ProjectiveRatioChartKernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

def projectiveChartCoordinateEmbedding
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) →ₐ[ℂ]
      FractionRing (CoordinateRing n ⧸ V.ideal.toIdeal) := by
  letI := V.prime
  exact Ideal.Quotient.liftₐ V.affineIdeal
    (coordinateRatioPolynomialMap (projectiveConeFractionCoordinates V))
    (fun P hP => RingHom.mem_ker.mp (projectiveRatioPolynomialMap_kernel V x hx ▸ hP))

theorem projectiveChartCoordinateEmbedding_mk
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) (P : MvPolynomial (Fin n) ℂ) :
    letI := V.prime
    projectiveChartCoordinateEmbedding V x hx (Ideal.Quotient.mk V.affineIdeal P) =
      coordinateRatioPolynomialMap (projectiveConeFractionCoordinates V) P := by
  letI := V.prime
  exact Ideal.Quotient.lift_mk _ _ _

theorem projectiveChartCoordinateEmbedding_injective
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    Function.Injective (projectiveChartCoordinateEmbedding V x hx) := by
  letI := V.prime
  exact RingHom.lift_injective_of_ker_le_ideal V.affineIdeal _
    (le_of_eq (projectiveRatioPolynomialMap_kernel V x hx))

theorem projectiveChartCoordinateEmbedding_range
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    (projectiveChartCoordinateEmbedding V x hx).range =
      Algebra.adjoin ℂ (Set.range (fun i : Fin n =>
        projectiveConeFractionCoordinates V i.succ / projectiveConeFractionCoordinates V 0)) := by
  letI := V.prime
  have he : (projectiveChartCoordinateEmbedding V x hx).range =
      (coordinateRatioPolynomialMap (projectiveConeFractionCoordinates V)).range := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact ⟨P, (projectiveChartCoordinateEmbedding_mk V x hx P).symm⟩
    · rintro ⟨P, rfl⟩
      exact ⟨Ideal.Quotient.mk V.affineIdeal P, projectiveChartCoordinateEmbedding_mk V x hx P⟩
  rw [he]
  exact MvPolynomial.aeval_range _

def projectiveChartFractionEmbedding
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := V.affineIdeal_isPrime_of_point x hx
    FractionRing (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) →ₐ[ℂ]
      FractionRing (CoordinateRing n ⧸ V.ideal.toIdeal) := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x hx
  exact IsFractionRing.liftAlgHom
    (K := FractionRing (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal))
    (projectiveChartCoordinateEmbedding_injective V x hx)

theorem projectiveChartFractionEmbedding_fieldRange
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := V.affineIdeal_isPrime_of_point x hx
    (projectiveChartFractionEmbedding V x hx).fieldRange = projectiveCoordinateRatioField V := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x hx
  exact IsFractionRing.liftAlgHom_fieldRange_eq_of_range_eq
    (projectiveChartCoordinateEmbedding_injective V x hx)
    (projectiveChartCoordinateEmbedding_range V x hx)

/-- An actual field isomorphism from the chart fraction field to the field of coordinate ratios. -/
def projectiveChartFractionRatioEquiv
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := V.affineIdeal_isPrime_of_point x hx
    FractionRing (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) ≃ₐ[ℂ]
      projectiveCoordinateRatioField V := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x hx
  exact (projectiveChartFractionEmbedding V x hx).equivFieldRange.trans
    (IntermediateField.equivOfEq (projectiveChartFractionEmbedding_fieldRange V x hx))

end LinearStudy
