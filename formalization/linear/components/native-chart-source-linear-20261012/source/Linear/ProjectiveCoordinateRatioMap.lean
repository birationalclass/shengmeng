module
public import Linear.ProjectiveCoordinateFractionMap
public import Linear.ProjectiveAffineVariety
public import Linear.HomogeneousRatioFieldMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

def projectiveConeFractionCoordinates (V : IntegralProjectiveEquations n) :
    letI := V.prime
    Fin (n + 1) → FractionRing (CoordinateRing n ⧸ V.ideal.toIdeal) := by
  letI := V.prime
  exact fun i => algebraMap _ _ (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X i))

theorem projectiveConeFractionCoordinates_aeval (V : IntegralProjectiveEquations n)
    (H : CoordinateRing n) :
    letI := V.prime
    MvPolynomial.aeval (projectiveConeFractionCoordinates V) H =
      algebraMap _ (FractionRing _) (Ideal.Quotient.mk V.ideal.toIdeal H) := by
  letI := V.prime
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  let F := FractionRing A
  have he : MvPolynomial.aeval (projectiveConeFractionCoordinates V) =
      (IsScalarTower.toAlgHom ℂ A F).comp (Ideal.Quotient.mkₐ ℂ V.ideal.toIdeal) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [MvPolynomial.aeval_X]
    change algebraMap A F (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X i)) = _
    rfl
  rw [he]
  rfl

theorem projectiveConeFractionCoordinates_zero_ne_zero
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    projectiveConeFractionCoordinates V 0 ≠ 0 := by
  letI := V.prime
  have hn : MvPolynomial.X (0 : Fin (n + 1)) ∉ V.ideal.toIdeal := by
    intro h
    have he := ((V.normalizedPoint_mem_iff x).mp hx) _ h
    simpa using he
  have hq : Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X (0 : Fin (n + 1))) ≠ 0 :=
    fun h => hn (Ideal.Quotient.eq_zero_iff_mem.mp h)
  exact fun h => hq ((IsFractionRing.injective (CoordinateRing n ⧸ V.ideal.toIdeal)
    (FractionRing (CoordinateRing n ⧸ V.ideal.toIdeal)))
    (by simpa [projectiveConeFractionCoordinates] using h))

theorem projectiveCoordinateFractionMap_coordinate
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (i : Fin (n + 1)) :
    letI := V.prime
    projectiveCoordinateFractionMap f V hq hf hV (projectiveConeFractionCoordinates V i) =
      MvPolynomial.aeval (projectiveConeFractionCoordinates V) (f.forms i) := by
  letI := V.prime
  rw [projectiveConeFractionCoordinates, projectiveCoordinateFractionMap_algebraMap,
    projectiveCoordinateDomainMap_mk, MvPolynomial.aeval_X,
    projectiveConeFractionCoordinates_aeval]

def projectiveCoordinateRatioField (V : IntegralProjectiveEquations n) :
    letI := V.prime
    IntermediateField ℂ (FractionRing (CoordinateRing n ⧸ V.ideal.toIdeal)) := by
  letI := V.prime
  exact coordinateRatioField (K := ℂ) (projectiveConeFractionCoordinates V)

/-- The actual f-induced map on the field of coordinate ratios of an inhabited chart.
The comparison with the fraction field of the dehomogenized chart is still separate. -/
def projectiveCoordinateRatioMap
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    projectiveCoordinateRatioField V →ₐ[ℂ] projectiveCoordinateRatioField V := by
  letI := V.prime
  exact coordinateRatioFieldMap (projectiveConeFractionCoordinates V)
    (projectiveConeFractionCoordinates_zero_ne_zero V x hx)
    (projectiveCoordinateFractionMap f V hq hf hV) f.forms f.homogeneous
    (projectiveCoordinateFractionMap_coordinate f V hq hf hV)

theorem projectiveCoordinateRatioMap_finite
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    (projectiveCoordinateRatioMap f V hq hf hV x hx).toRingHom.Finite := by
  letI := V.prime
  exact coordinateRatioFieldMap_finite _
    (projectiveConeFractionCoordinates_zero_ne_zero V x hx)
    (projectiveCoordinateFractionMap f V hq hf hV) f.forms f.homogeneous
    (projectiveCoordinateFractionMap_coordinate f V hq hf hV)

theorem projectiveCoordinateRatioMap_formallyUnramified
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    (projectiveCoordinateRatioMap f V hq hf hV x hx).toRingHom.FormallyUnramified := by
  letI := V.prime
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  let F := FractionRing A
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap ℂ F).injective
  exact coordinateRatioFieldMap_formallyUnramified _
    (projectiveConeFractionCoordinates_zero_ne_zero V x hx)
    (projectiveCoordinateFractionMap f V hq hf hV) f.forms f.homogeneous
    (projectiveCoordinateFractionMap_coordinate f V hq hf hV)

end LinearStudy
