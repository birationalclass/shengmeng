module
public import Linear.ProjectiveGeneralResidueSurjective
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Basis.Defs
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} {σ : Type} [CommRing R] [Fintype σ] [LinearOrder σ]

/-- Reuse mathlib's actual restricted-support monomial basis, transported
to its actual homogeneous polynomial submodule. -/
def projectiveHomogeneousMonomialBasis (m : ℕ) :
    Module.Basis (ProjectiveMonomialIndex σ m) R (homogeneousSubmodule σ R m) :=
  (basisRestrictSupport R {a : σ →₀ ℕ | a.degree = m}).map
    (LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported σ R m).symm)

/-- Negative coefficients define every functional on actual homogeneous
polynomials uniquely, by the complementary monomial basis. -/
def projectiveNegativeCoordinatesDualEquiv (m : ℕ) :
    (ProjectiveNegativeWeight σ m → R) ≃ₗ[R]
      Module.Dual R (homogeneousSubmodule σ R m) :=
  (LinearEquiv.piCongrLeft' R (fun _ : ProjectiveNegativeWeight σ m => R)
    (projectiveNegativeWeightEquivMonomial m)).trans
      ((projectiveHomogeneousMonomialBasis (R := R) (σ := σ) m).constr R)

/-- Actual Laurent top quotient duality against the actual homogeneous
polynomial module. This alone does not assert sheaf-derived proper duality. -/
def coordinateGeneralTopQuotientDualEquiv (m n : ℕ) (hc : Fintype.card σ = n+2) :
    (coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) (-(m : ℤ)-Fintype.card σ) (n+1) ⧸
      LinearMap.range (coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) (-(m : ℤ)-Fintype.card σ) n).hom)
      ≃ₗ[coordinateCanonicalBaseRing R]
      Module.Dual (coordinateCanonicalBaseRing R)
        (homogeneousSubmodule σ (coordinateCanonicalBaseRing R) m) :=
  (coordinateGeneralTopQuotientEquiv (R := R) m n hc).trans
    (projectiveNegativeCoordinatesDualEquiv m)

/-- On a monomial basis vector the functional extracts precisely its
complementary all-negative Laurent coefficient. -/
theorem projectiveNegativeCoordinatesDualEquiv_apply_basis (m : ℕ)
    (v : ProjectiveNegativeWeight σ m → R) (a : ProjectiveMonomialIndex σ m) :
    projectiveNegativeCoordinatesDualEquiv m v
      (projectiveHomogeneousMonomialBasis (R := R) m a) =
      v (projectiveMonomialNegativeWeight m a) := by
  simp [projectiveNegativeCoordinatesDualEquiv,Module.Basis.constr_basis]
  rfl
end MvPolynomial
