module
public import Linear.CoordinateRatioField
public import Linear.FieldEndomorphismMap
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
variable {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}

theorem homogeneous_ratio_eq_chart_ratio (x : Fin (n + 1) → F) (hx : x 0 ≠ 0)
    (H H₀ : MvPolynomial (Fin (n + 1)) K) {q : ℕ}
    (hH : H.IsHomogeneous q) (hH₀ : H₀.IsHomogeneous q) :
    MvPolynomial.aeval x H / MvPolynomial.aeval x H₀ =
      coordinateRatioPolynomialMap x (affineChartPolynomialMap H) /
        coordinateRatioPolynomialMap x (affineChartPolynomialMap H₀) := by
  rw [coordinateRatioPolynomialMap_homogeneous x hx H hH,
    coordinateRatioPolynomialMap_homogeneous x hx H₀ hH₀]
  exact (mul_div_mul_left _ _ (pow_ne_zero q (inv_ne_zero hx))).symm

theorem homogeneous_ratio_mem_coordinateRatioField (x : Fin (n + 1) → F) (hx : x 0 ≠ 0)
    (H H₀ : MvPolynomial (Fin (n + 1)) K) {q : ℕ}
    (hH : H.IsHomogeneous q) (hH₀ : H₀.IsHomogeneous q) :
    MvPolynomial.aeval x H / MvPolynomial.aeval x H₀ ∈ coordinateRatioField (K := K) x := by
  rw [homogeneous_ratio_eq_chart_ratio x hx H H₀ hH hH₀]
  exact (coordinateRatioField (K := K) x).div_mem
    (coordinateRatioPolynomialMap_mem x _) (coordinateRatioPolynomialMap_mem x _)

/-- Stability follows from the actual homogeneous coordinate formulas. -/
theorem coordinateRatioField_le_comap
    (x : Fin (n + 1) → F) (hx : x 0 ≠ 0) (φ : F →ₐ[K] F)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) {q : ℕ}
    (hp : ∀ i, (p i).IsHomogeneous q) (hφ : ∀ i, φ (x i) = MvPolynomial.aeval x (p i)) :
    coordinateRatioField (K := K) x ≤ (coordinateRatioField (K := K) x).comap φ := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨i, rfl⟩
  change φ (x i.succ / x 0) ∈ coordinateRatioField (K := K) x
  rw [map_div₀, hφ i.succ, hφ 0]
  exact homogeneous_ratio_mem_coordinateRatioField x hx _ _ (hp i.succ) (hp 0)

/-- Restrict the actual ambient field map to the coordinate-ratio field. -/
def coordinateRatioFieldMap
    (x : Fin (n + 1) → F) (hx : x 0 ≠ 0) (φ : F →ₐ[K] F)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) {q : ℕ}
    (hp : ∀ i, (p i).IsHomogeneous q) (hφ : ∀ i, φ (x i) = MvPolynomial.aeval x (p i)) :
    coordinateRatioField (K := K) x →ₐ[K] coordinateRatioField (K := K) x :=
  (φ.comp (coordinateRatioField (K := K) x).val).codRestrict
    (coordinateRatioField (K := K) x).toSubalgebra
    (fun z => coordinateRatioField_le_comap x hx φ p hp hφ z.property)

theorem coordinateRatioFieldMap_finite
    (x : Fin (n + 1) → F) (hx : x 0 ≠ 0) (φ : F →ₐ[K] F)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) {q : ℕ}
    (hp : ∀ i, (p i).IsHomogeneous q) (hφ : ∀ i, φ (x i) = MvPolynomial.aeval x (p i)) :
    (coordinateRatioFieldMap x hx φ p hp hφ).toRingHom.Finite := by
  letI : Algebra.EssFiniteType K (coordinateRatioField (K := K) x) := coordinateRatioField_essFiniteType x
  exact fieldEndomorphism_finite _

theorem coordinateRatioFieldMap_formallyUnramified [CharZero F]
    (x : Fin (n + 1) → F) (hx : x 0 ≠ 0) (φ : F →ₐ[K] F)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) {q : ℕ}
    (hp : ∀ i, (p i).IsHomogeneous q) (hφ : ∀ i, φ (x i) = MvPolynomial.aeval x (p i)) :
    (coordinateRatioFieldMap x hx φ p hp hφ).toRingHom.FormallyUnramified := by
  letI : Algebra.EssFiniteType K (coordinateRatioField (K := K) x) := coordinateRatioField_essFiniteType x
  exact fieldEndomorphism_formallyUnramified _

end LinearStudy
