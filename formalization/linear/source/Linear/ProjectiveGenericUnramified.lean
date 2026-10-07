module
public import Linear.ProjectiveCoordinateGenericMap
public import Mathlib.RingTheory.RingHom.FiniteType
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- The actual coordinate-domain map is of finite type, without an
additional finite-type hypothesis on the map. -/
theorem projectiveCoordinateDomainMap_finiteType
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    (projectiveCoordinateDomainMap f V hq hf hV).toRingHom.FiniteType := by
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveCoordinateDomainMap f V hq hf hV
  have he : φ.toRingHom.comp (algebraMap ℂ A) = algebraMap ℂ A := by
    ext a
    exact φ.commutes a
  have hc : (φ.toRingHom.comp (algebraMap ℂ A)).FiniteType := by
    rw [he, RingHom.finiteType_algebraMap]
    infer_instance
  exact RingHom.FiniteType.of_comp_finiteType hc

/-- Nonramification over the source coordinate ring at the generic point
is obtained from the actual fraction-field map. -/
theorem projectiveCoordinateDomainMap_fraction_comp_formallyUnramified
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    letI := V.prime
    ((algebraMap (CoordinateRing n ⧸ V.ideal.toIdeal)
        (FractionRing (CoordinateRing n ⧸ V.ideal.toIdeal))).comp
      (projectiveCoordinateDomainMap f V hq hf hV).toRingHom).FormallyUnramified := by
  letI := V.prime
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  let F := FractionRing A
  have hi : (algebraMap A F).FormallyUnramified :=
    RingHom.formallyUnramified_algebraMap.mpr
      (Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors A))
  have hc := hi.comp (projectiveCoordinateFractionMap_formallyUnramified f V hq hf hV)
  have he : (projectiveCoordinateFractionMap f V hq hf hV).toRingHom.comp (algebraMap A F) =
      (algebraMap A F).comp (projectiveCoordinateDomainMap f V hq hf hV).toRingHom := by
    apply RingHom.ext
    intro a
    exact projectiveCoordinateFractionMap_algebraMap f V hq hf hV a
  rw [he] at hc
  exact hc

end LinearStudy
