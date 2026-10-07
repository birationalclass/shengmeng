module
public import Linear.ProjectiveCoordinateFractionMap
public import Linear.FieldEndomorphismMap
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- The actual induced map on the cone function field is finite. -/
theorem projectiveCoordinateFractionMap_finite
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    letI := V.prime
    (projectiveCoordinateFractionMap f V hq hf hV).toRingHom.Finite := by
  letI := V.prime
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  let F := FractionRing A
  letI : Algebra.EssFiniteType A F := Algebra.EssFiniteType.of_isLocalization F (nonZeroDivisors A)
  letI : Algebra.EssFiniteType ℂ F := Algebra.EssFiniteType.comp ℂ A F
  exact fieldEndomorphism_finite (projectiveCoordinateFractionMap f V hq hf hV)

/-- Formal nonramification of the actual cone function-field map,
derived from the original projective hypotheses in characteristic zero. -/
theorem projectiveCoordinateFractionMap_formallyUnramified
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    letI := V.prime
    (projectiveCoordinateFractionMap f V hq hf hV).toRingHom.FormallyUnramified := by
  letI := V.prime
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  let F := FractionRing A
  letI : Algebra.EssFiniteType A F := Algebra.EssFiniteType.of_isLocalization F (nonZeroDivisors A)
  letI : Algebra.EssFiniteType ℂ F := Algebra.EssFiniteType.comp ℂ A F
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap ℂ F).injective
  exact fieldEndomorphism_formallyUnramified (projectiveCoordinateFractionMap f V hq hf hV)

end LinearStudy
