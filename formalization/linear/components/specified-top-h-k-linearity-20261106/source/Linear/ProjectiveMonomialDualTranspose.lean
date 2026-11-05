module
public import Linear.ProjectiveHomogeneousBasisProduct
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
variable {R : Type} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]

/-- Complementary coefficient shift, defined by original exponent addition
and independently of the actual polynomial dual map. -/
def projectiveNegativeCoordinatesMonomialShift (l m : ℕ)
    (b : ProjectiveMonomialIndex σ l) (v : ProjectiveNegativeWeight σ (l+m) → R) :
    ProjectiveNegativeWeight σ m → R := fun e =>
  v (projectiveMonomialNegativeWeight (l+m)
    (projectiveMonomialIndexAdd l m b (projectiveNegativeWeightEquivMonomial m e)))

/-- Precomposition with actual monomial multiplication extracts exactly
the complementary coefficient indexed by the sum of original exponents. -/
theorem projectiveMonomialMultiplyDual_apply_basis (l m : ℕ)
    (b : ProjectiveMonomialIndex σ l) (c : ProjectiveMonomialIndex σ m)
    (v : ProjectiveNegativeWeight σ (l+m) → R) :
    projectiveHomogeneousMultiplyDual l m (projectiveHomogeneousMonomialBasis (R := R) l b)
      (projectiveNegativeCoordinatesDualEquiv (l+m) v)
      (projectiveHomogeneousMonomialBasis (R := R) m c) =
    v (projectiveMonomialNegativeWeight (l+m) (projectiveMonomialIndexAdd l m b c)) := by
  rw [projectiveHomogeneousMultiplyDual_apply, projectiveHomogeneousMultiply_basis,
    projectiveNegativeCoordinatesDualEquiv_apply_basis]

/-- The complementary-coordinate duality intertwines coefficient shift
with the transpose of ACTUAL polynomial multiplication. Connection of
these coordinates to the native top-Cech residue map is a separate step. -/
theorem projectiveMonomialMultiplyDual_coordinate_naturality (l m : ℕ)
    (b : ProjectiveMonomialIndex σ l) (v : ProjectiveNegativeWeight σ (l+m) → R) :
    projectiveNegativeCoordinatesDualEquiv m (projectiveNegativeCoordinatesMonomialShift l m b v) =
    projectiveHomogeneousMultiplyDual l m (projectiveHomogeneousMonomialBasis (R := R) l b)
      (projectiveNegativeCoordinatesDualEquiv (l+m) v) := by
  apply (projectiveHomogeneousMonomialBasis (R := R) m).ext
  intro c
  rw [projectiveNegativeCoordinatesDualEquiv_apply_basis,
    projectiveMonomialMultiplyDual_apply_basis]
  change v (projectiveMonomialNegativeWeight (l+m)
    (projectiveMonomialIndexAdd l m b
      ((projectiveNegativeWeightEquivMonomial m)
        ((projectiveNegativeWeightEquivMonomial m).symm c)))) = _
  rw [Equiv.apply_symm_apply]
end MvPolynomial
