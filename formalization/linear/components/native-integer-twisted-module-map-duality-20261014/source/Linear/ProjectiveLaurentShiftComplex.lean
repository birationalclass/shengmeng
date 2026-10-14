module
public import Linear.ProjectiveLaurentCechShift
public import Linear.NativeProjectiveLaurentComplex
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory
universe u
variable {K : Type u} [Field K] {σ : Type} [LinearOrder σ] {d l : ℤ}

/-- The exponent shift is an actual cochain morphism of Laurent complexes.
Identification with the native sheaf multiplication map is still separate. -/
def coordinateLaurentShiftComplex (b : HomogeneousLaurentExponent σ l)
    (hb : ∀ i, 0 ≤ b.1 i) :
    coordinateNativeLaurentOrderedCechComplex (K := K) (σ := σ) d ⟶
      coordinateNativeLaurentOrderedCechComplex (K := K) (σ := σ) (d+l) where
  f n := coordinateLaurentCechShift b hb n
  comm' n m h := by
    simp only [ComplexShape.up_Rel] at h
    subst m
    rw [coordinateNativeLaurentOrderedCechComplex_d,
      coordinateNativeLaurentOrderedCechComplex_d]
    exact coordinateLaurentCechShift_differential b hb n

/-- Functorial homology map of the constructed cochain morphism. -/
def coordinateLaurentShiftHomology (b : HomogeneousLaurentExponent σ l)
    (hb : ∀ i, 0 ≤ b.1 i) (n : ℕ) :
    (coordinateNativeLaurentOrderedCechComplex (K := K) (σ := σ) d).homology n ⟶
      (coordinateNativeLaurentOrderedCechComplex (K := K) (σ := σ) (d+l)).homology n :=
  HomologicalComplex.homologyMap (coordinateLaurentShiftComplex b hb) n
end MvPolynomial
