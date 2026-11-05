module
public import Linear.ProjectiveLaurentDegreeTransport
public import Linear.NativeProjectiveLaurentComplex
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory
variable {K : Type} [Field K] {σ : Type} [LinearOrder σ] {d d' : ℤ}

def coordinateLaurentComplexDegreeCast (h : d=d') :
    coordinateNativeLaurentOrderedCechComplex (K := K) (σ := σ) d ⟶
    coordinateNativeLaurentOrderedCechComplex (K := K) (σ := σ) d' :=
  (eqToIso (congrArg (fun q => coordinateNativeLaurentOrderedCechComplex
    (K := K) (σ := σ) q) h)).hom

def coordinateNativeComplexDegreeCast (h : d=d') :
    Scheme.Modules.orderedBaseCechComplex (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) d) (coordinateOpenCover (R := K) (σ := σ)) ⟶
    Scheme.Modules.orderedBaseCechComplex (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) d') (coordinateOpenCover (R := K) (σ := σ)) :=
  (eqToIso (congrArg (fun q => Scheme.Modules.orderedBaseCechComplex
    (homogeneousProjπ (R := K) (σ := σ)) (coordinateNativeIntegerTwist (K := K) (σ := σ) q)
      (coordinateOpenCover (R := K) (σ := σ))) h)).hom

theorem coordinateLaurentComplexDegreeCast_f (h : d=d') (n : ℕ) :
    (coordinateLaurentComplexDegreeCast (K := K) (σ := σ) h).f n =
      ModuleCat.ofHom (coordinateLaurentCechDegreeCast (R := K) (σ := σ) h n) := by
  cases h
  apply ModuleCat.hom_ext
  ext s
  rfl

/-- The previously constructed native/Laurent comparison commutes with
genuine equality transport in the integer degree. -/
theorem coordinateNativeLaurentComplexDegreeCast_naturality (h : d=d') :
    (coordinateNativeLaurentOrderedCechComplexIso (K := K) (σ := σ) d).hom ≫
      coordinateLaurentComplexDegreeCast (K := K) (σ := σ) h =
    coordinateNativeComplexDegreeCast (K := K) (σ := σ) h ≫
      (coordinateNativeLaurentOrderedCechComplexIso (K := K) (σ := σ) d').hom := by
  cases h
  simp [coordinateLaurentComplexDegreeCast, coordinateNativeComplexDegreeCast]

end MvPolynomial
