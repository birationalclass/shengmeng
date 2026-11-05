module
public import Linear.ProjectiveMonomialResidueNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory
variable {R : Type} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]

/-- The actual top coefficient map, evaluated on actual homogeneous
polynomials using the already proved complementary monomial basis. -/
def coordinateGeneralResiduePairing (m n : ℕ) (hc : Fintype.card σ = n+1) :
    coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ)
      (-(m:ℤ)-Fintype.card σ) n →ₗ[coordinateCanonicalBaseRing R]
    Module.Dual (coordinateCanonicalBaseRing R)
      (homogeneousSubmodule σ (coordinateCanonicalBaseRing R) m) :=
  (projectiveNegativeCoordinatesDualEquiv m).toLinearMap.comp
    (coordinateGeneralResidue (R := R) m n hc)

/-- The actual top coefficient map intertwines the independently
constructed monomial Cech multiplication with complementary-coordinate shift. -/
theorem coordinateGeneralResidue_monomial_naturality (l m n : ℕ)
    (hc : Fintype.card σ = n+1) (b : ProjectiveMonomialIndex σ l)
    (s : coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ)
      (-((l+m:ℕ):ℤ)-Fintype.card σ) n) :
    coordinateGeneralResidue (R := R) m n hc
      (coordinateComplementaryMonomialCechShift l m b n s) =
    projectiveNegativeCoordinatesMonomialShift l m b
      (coordinateGeneralResidue (R := R) (l+m) n hc s) := by
  funext e
  exact coordinateGeneralResidue_monomial_shift l m n hc b s e

/-- Actual monomial multiplication on top Cech cochains is transpose
to actual multiplication of homogeneous polynomials under the residue pairing. -/
theorem coordinateGeneralResiduePairing_monomial_naturality (l m n : ℕ)
    (hc : Fintype.card σ = n+1) (b : ProjectiveMonomialIndex σ l)
    (s : coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ)
      (-((l+m:ℕ):ℤ)-Fintype.card σ) n) :
    coordinateGeneralResiduePairing (R := R) m n hc
      (coordinateComplementaryMonomialCechShift l m b n s) =
    projectiveHomogeneousMultiplyDual l m
      (projectiveHomogeneousMonomialBasis (R := coordinateCanonicalBaseRing R) l b)
      (coordinateGeneralResiduePairing (R := R) (l+m) n hc s) := by
  change projectiveNegativeCoordinatesDualEquiv m
      (coordinateGeneralResidue (R := R) m n hc
        (coordinateComplementaryMonomialCechShift l m b n s)) =
    projectiveHomogeneousMultiplyDual l m _
      (projectiveNegativeCoordinatesDualEquiv (l+m)
        (coordinateGeneralResidue (R := R) (l+m) n hc s))
  rw [coordinateGeneralResidue_monomial_naturality]
  exact projectiveMonomialMultiplyDual_coordinate_naturality l m b _

end MvPolynomial
