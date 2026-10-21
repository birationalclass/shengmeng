module
public import Linear.ProjectiveLaurentCechShiftCoefficients
public import Linear.ProjectiveLaurentDegreeTransport
public import Linear.ProjectivePositiveMonomialWeight
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory
universe u
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]

theorem projectiveComplementaryShiftDegree (l m : ℕ) :
    -((l+m:ℕ):ℤ)-Fintype.card σ+(l:ℤ) = -(m:ℤ)-Fintype.card σ := by
  simp only [Nat.cast_add]
  omega

/-- Actual monomial Cech shift followed by explicitly proved integer-degree
equality transport. It is not constructed from residue or duality coordinates. -/
def coordinateComplementaryMonomialCechShift (l m : ℕ)
    (b : ProjectiveMonomialIndex σ l) (n : ℕ) :
    coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ)
      (-((l+m:ℕ):ℤ)-Fintype.card σ) n →ₗ[coordinateCanonicalBaseRing R]
    coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ)
      (-(m:ℤ)-Fintype.card σ) n :=
  (coordinateLaurentCechDegreeCast (R := R) (projectiveComplementaryShiftDegree (σ := σ) l m) n).comp
    (coordinateLaurentCechShift (R := R) (d := -((l+m:ℕ):ℤ)-Fintype.card σ)
      (projectiveMonomialPositiveWeight l b)
      (projectiveMonomialPositiveWeight_nonnegative l b) n).hom

/-- The complementary source exponent is sent to the complementary target
exponent after the actual monomial shift and degree equality transport. -/
theorem projectiveComplementaryShiftWeight (l m : ℕ)
    (b : ProjectiveMonomialIndex σ l) (c : ProjectiveMonomialIndex σ m)
    {n : ℕ} (a : Fin (n+1) → σ)
    (hs : (projectiveMonomialNegativeWeight (l+m) (projectiveMonomialIndexAdd l m b c)).1.IsAllowedOn a) :
    homogeneousLaurentWeightDegreeCast (projectiveComplementaryShiftDegree (σ := σ) l m)
      (homogeneousLaurentAllowedShift a (projectiveMonomialPositiveWeight l b)
        (projectiveMonomialPositiveWeight_nonnegative l b)
        ⟨(projectiveMonomialNegativeWeight (l+m) (projectiveMonomialIndexAdd l m b c)).1, hs⟩).1 =
      (projectiveMonomialNegativeWeight m c).1 := by
  apply Subtype.ext
  rw [homogeneousLaurentWeightDegreeCast_val]
  ext i
  change (projectiveMonomialNegativeWeight (l+m) (projectiveMonomialIndexAdd l m b c)).1.1 i +
    (projectiveMonomialPositiveWeight l b).1 i = (projectiveMonomialNegativeWeight m c).1.1 i
  simp only [projectiveMonomialNegativeWeight_apply, projectiveMonomialPositiveWeight_apply,
    projectiveMonomialIndexAdd, Finsupp.add_apply, Nat.cast_add]
  ring
end MvPolynomial
