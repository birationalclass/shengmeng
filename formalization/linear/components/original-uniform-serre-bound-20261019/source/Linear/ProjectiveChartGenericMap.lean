module
public import Linear.ProjectiveChartFractionField
public import Linear.FieldEndomorphismMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

theorem projectiveChartFractionRatioEquiv_val
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := V.affineIdeal_isPrime_of_point x hx
    ∀ z : FractionRing (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal),
      ((projectiveChartFractionRatioEquiv V x hx z : projectiveCoordinateRatioField V) :
        FractionRing (CoordinateRing n ⧸ V.ideal.toIdeal)) =
          projectiveChartFractionEmbedding V x hx z := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x hx
  intro z
  rfl

def projectiveChartFractionMap
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := V.affineIdeal_isPrime_of_point x hx
    FractionRing (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) →ₐ[ℂ]
      FractionRing (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x hx
  let e := projectiveChartFractionRatioEquiv V x hx
  exact e.symm.toAlgHom.comp ((projectiveCoordinateRatioMap f V hq hf hV x hx).comp e.toAlgHom)

theorem projectiveChartFractionMap_commutes
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := V.affineIdeal_isPrime_of_point x hx
    ∀ z : FractionRing (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal),
      projectiveChartFractionEmbedding V x hx (projectiveChartFractionMap f V hq hf hV x hx z) =
        projectiveCoordinateFractionMap f V hq hf hV (projectiveChartFractionEmbedding V x hx z) := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x hx
  intro z
  rw [← projectiveChartFractionRatioEquiv_val V x hx]
  change ((projectiveChartFractionRatioEquiv V x hx
      ((projectiveChartFractionRatioEquiv V x hx).symm
        (projectiveCoordinateRatioMap f V hq hf hV x hx
          (projectiveChartFractionRatioEquiv V x hx z)))) :
      FractionRing (CoordinateRing n ⧸ V.ideal.toIdeal)) = _
  rw [AlgEquiv.apply_symm_apply]
  change projectiveCoordinateFractionMap f V hq hf hV
      ((projectiveChartFractionRatioEquiv V x hx z : projectiveCoordinateRatioField V) : _) = _
  rw [projectiveChartFractionRatioEquiv_val]

theorem projectiveChartFractionMap_finite
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := V.affineIdeal_isPrime_of_point x hx
    (projectiveChartFractionMap f V hq hf hV x hx).toRingHom.Finite := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x hx
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let L := FractionRing B
  letI : Algebra.EssFiniteType B L := Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors B)
  letI : Algebra.EssFiniteType ℂ L := Algebra.EssFiniteType.comp ℂ B L
  exact fieldEndomorphism_finite _

theorem projectiveChartFractionMap_formallyUnramified
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := V.affineIdeal_isPrime_of_point x hx
    (projectiveChartFractionMap f V hq hf hV x hx).toRingHom.FormallyUnramified := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x hx
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let L := FractionRing B
  letI : Algebra.EssFiniteType B L := Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors B)
  letI : Algebra.EssFiniteType ℂ L := Algebra.EssFiniteType.comp ℂ B L
  letI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℂ L).injective
  exact fieldEndomorphism_formallyUnramified _

end LinearStudy
