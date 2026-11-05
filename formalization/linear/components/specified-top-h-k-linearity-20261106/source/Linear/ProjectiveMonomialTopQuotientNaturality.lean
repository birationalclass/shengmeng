module
public import Linear.ProjectiveMonomialResidueDuality
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory
variable {R : Type} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]

abbrev coordinateGeneralTopBoundaries (m n : ℕ) :=
  LinearMap.range (coordinateHomogeneousLaurentOrderedCechDifferential
    (R := R) (σ := σ) (-(m:ℤ)-Fintype.card σ) n).hom

/-- Actual monomial multiplication sends actual top Cech boundaries to
actual boundaries. The proof uses the already verified residue kernel theorem. -/
theorem coordinateComplementaryMonomialCechShift_preserves_boundaries (l m n : ℕ)
    (hc : Fintype.card σ = n+2) (b : ProjectiveMonomialIndex σ l) :
    coordinateGeneralTopBoundaries (R := R) (σ := σ) (l+m) n ≤
      (coordinateGeneralTopBoundaries (R := R) (σ := σ) m n).comap
        (coordinateComplementaryMonomialCechShift l m b (n+1)) := by
  intro s hs
  change coordinateComplementaryMonomialCechShift l m b (n+1) s ∈
    coordinateGeneralTopBoundaries (R := R) (σ := σ) m n
  have hz : coordinateGeneralResidue (R := R) (l+m) (n+1) hc s = 0 := by
    apply LinearMap.mem_ker.mp
    rw [coordinateGeneralResidue_ker_eq_range]
    exact hs
  unfold coordinateGeneralTopBoundaries
  rw [← coordinateGeneralResidue_ker_eq_range (R := R) m n hc]
  apply LinearMap.mem_ker.mpr
  funext e
  rw [coordinateGeneralResidue_monomial_shift]
  exact congrFun hz _

/-- The quotient map induced by actual Cech multiplication, not by
transporting the polynomial dual map through an equivalence. -/
def coordinateComplementaryMonomialTopQuotientMap (l m n : ℕ)
    (hc : Fintype.card σ = n+2) (b : ProjectiveMonomialIndex σ l) :
    (coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ)
      (-((l+m:ℕ):ℤ)-Fintype.card σ) (n+1) ⧸
        coordinateGeneralTopBoundaries (R := R) (σ := σ) (l+m) n) →ₗ[coordinateCanonicalBaseRing R]
    (coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ)
      (-(m:ℤ)-Fintype.card σ) (n+1) ⧸
        coordinateGeneralTopBoundaries (R := R) (σ := σ) m n) :=
  Submodule.mapQ _ _ (coordinateComplementaryMonomialCechShift l m b (n+1))
    (coordinateComplementaryMonomialCechShift_preserves_boundaries l m n hc b)

theorem coordinateComplementaryMonomialTopQuotientMap_mk (l m n : ℕ)
    (hc : Fintype.card σ = n+2) (b : ProjectiveMonomialIndex σ l)
    (s : coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ)
      (-((l+m:ℕ):ℤ)-Fintype.card σ) (n+1)) :
    coordinateComplementaryMonomialTopQuotientMap l m n hc b (Submodule.Quotient.mk s) =
      Submodule.Quotient.mk (coordinateComplementaryMonomialCechShift l m b (n+1) s) := rfl

/-- The previously proved actual top quotient duality evaluates on a
representative by its actual Cech residue pairing. -/
theorem coordinateGeneralTopQuotientDualEquiv_mk (m n : ℕ)
    (hc : Fintype.card σ = n+2)
    (s : coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ)
      (-(m:ℤ)-Fintype.card σ) (n+1)) :
    coordinateGeneralTopQuotientDualEquiv (R := R) m n hc (Submodule.Quotient.mk s) =
      coordinateGeneralResiduePairing (R := R) m (n+1) hc s := by
  simp [coordinateGeneralTopQuotientDualEquiv, coordinateGeneralTopQuotientEquiv,
    coordinateGeneralResiduePairing]

/-- The actual top Cech quotient duality intertwines multiplication by
X^b with the transpose of actual homogeneous polynomial multiplication. -/
theorem coordinateGeneralTopQuotientDualEquiv_monomial_naturality (l m n : ℕ)
    (hc : Fintype.card σ = n+2) (b : ProjectiveMonomialIndex σ l)
    (s : coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ)
      (-((l+m:ℕ):ℤ)-Fintype.card σ) (n+1) ⧸
        coordinateGeneralTopBoundaries (R := R) (σ := σ) (l+m) n) :
    coordinateGeneralTopQuotientDualEquiv (R := R) m n hc
      (coordinateComplementaryMonomialTopQuotientMap l m n hc b s) =
    projectiveHomogeneousMultiplyDual l m
      (projectiveHomogeneousMonomialBasis (R := coordinateCanonicalBaseRing R) l b)
      (coordinateGeneralTopQuotientDualEquiv (R := R) (l+m) n hc s) := by
  induction s using Submodule.Quotient.induction_on with
  | _ s =>
    rw [coordinateComplementaryMonomialTopQuotientMap_mk,
      coordinateGeneralTopQuotientDualEquiv_mk, coordinateGeneralTopQuotientDualEquiv_mk]
    exact coordinateGeneralResiduePairing_monomial_naturality l m (n+1) hc b s

end MvPolynomial
