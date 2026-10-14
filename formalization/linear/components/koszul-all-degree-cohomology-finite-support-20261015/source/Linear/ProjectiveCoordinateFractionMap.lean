module
public import Linear.ProjectiveCoordinateDomainMap
public import Linear.FiniteTypeFieldEndomorphism
public import Mathlib.RingTheory.Localization.FractionRing
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- The actual fraction-field map of the homogeneous coordinate domain.
This is the cone function field, not yet the degree-zero projective field. -/
def projectiveCoordinateFractionMap
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    letI := V.prime
    FractionRing (CoordinateRing n ⧸ V.ideal.toIdeal) →ₐ[ℂ]
      FractionRing (CoordinateRing n ⧸ V.ideal.toIdeal) := by
  letI := V.prime
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  let F := FractionRing A
  let φ := (IsScalarTower.toAlgHom ℂ A F).comp (projectiveCoordinateDomainMap f V hq hf hV)
  have hi : Function.Injective φ :=
    (IsFractionRing.injective A F).comp (projectiveCoordinateDomainMap_injective f V hq hf hV)
  exact IsFractionRing.liftAlgHom (K := F) hi

theorem projectiveCoordinateFractionMap_algebraMap
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    letI := V.prime
    ∀ a : CoordinateRing n ⧸ V.ideal.toIdeal,
      projectiveCoordinateFractionMap f V hq hf hV (algebraMap _ (FractionRing _) a) =
        algebraMap _ (FractionRing _) (projectiveCoordinateDomainMap f V hq hf hV a) := by
  letI := V.prime
  intro a
  unfold projectiveCoordinateFractionMap
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  let F := FractionRing A
  let φ := (IsScalarTower.toAlgHom ℂ A F).comp (projectiveCoordinateDomainMap f V hq hf hV)
  have hi : Function.Injective φ :=
    (IsFractionRing.injective A F).comp (projectiveCoordinateDomainMap_injective f V hq hf hV)
  exact IsFractionRing.lift_algebraMap hi a

theorem projectiveCoordinateFractionMap_range_finite
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    letI := V.prime
    Module.Finite (projectiveCoordinateFractionMap f V hq hf hV).fieldRange
      (FractionRing (CoordinateRing n ⧸ V.ideal.toIdeal)) := by
  letI := V.prime
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  let F := FractionRing A
  letI : Algebra.EssFiniteType A F := Algebra.EssFiniteType.of_isLocalization F (nonZeroDivisors A)
  letI : Algebra.EssFiniteType ℂ F := Algebra.EssFiniteType.comp ℂ A F
  exact fieldEndomorphism_range_finite (projectiveCoordinateFractionMap f V hq hf hV)

theorem projectiveCoordinateFractionMap_range_formallyUnramified
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    letI := V.prime
    Algebra.FormallyUnramified (projectiveCoordinateFractionMap f V hq hf hV).fieldRange
      (FractionRing (CoordinateRing n ⧸ V.ideal.toIdeal)) := by
  letI := V.prime
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  let F := FractionRing A
  letI : Algebra.EssFiniteType A F := Algebra.EssFiniteType.of_isLocalization F (nonZeroDivisors A)
  letI : Algebra.EssFiniteType ℂ F := Algebra.EssFiniteType.comp ℂ A F
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap ℂ F).injective
  exact fieldEndomorphism_range_formallyUnramified (projectiveCoordinateFractionMap f V hq hf hV)

end LinearStudy
