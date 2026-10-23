module
public import Linear.ProjectiveGeneralResidueCoordinates
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {σ : Type} [LinearOrder σ] {d d' : ℤ}

def homogeneousLaurentWeightDegreeCast (h : d=d') (e : HomogeneousLaurentExponent σ d) :
    HomogeneousLaurentExponent σ d' := h ▸ e

theorem homogeneousLaurentWeightDegreeCast_val (h : d=d') (e : HomogeneousLaurentExponent σ d) :
    (homogeneousLaurentWeightDegreeCast h e).1 = e.1 := by cases h; rfl

/-- Genuine equality transport between the actual degree-indexed Cech objects. -/
def coordinateLaurentCechDegreeCast (h : d=d') (n : ℕ) :
    coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n →ₗ[
      coordinateCanonicalBaseRing R]
    coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d' n :=
  (eqToIso (congrArg (fun q => coordinateHomogeneousLaurentOrderedCechObject
    (R := R) (σ := σ) q n) h)).toLinearEquiv.toLinearMap

theorem coordinateLaurentCechDegreeCast_weightComponent (h : d=d')
    (e : HomogeneousLaurentExponent σ d) {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n)
    (s : coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n) :
    (coordinateHomogeneousLaurentWeightComponent (R := R) d'
      (homogeneousLaurentWeightDegreeCast h e) n
        (coordinateLaurentCechDegreeCast (R := R) h n s)).1 a =
    (coordinateHomogeneousLaurentWeightComponent (R := R) d e n s).1 a := by
  cases h
  rfl
end MvPolynomial
