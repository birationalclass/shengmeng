module
public import Linear.ProjectiveAffineVariety
public import Mathlib.RingTheory.Localization.Integer
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- Clear the actual affine-chart denominator without asserting that an
arbitrary target polynomial is homogeneous. -/
theorem projectiveChartPolynomial_exists_cone_numerator
    (V : IntegralProjectiveEquations n) (p : MvPolynomial (Fin n) ℂ)
    (hp : p ∉ V.affineIdeal) :
    ∃ (H : CoordinateRing n) (k : ℕ), H ∉ V.ideal.toIdeal ∧
      algebraMap (CoordinateRing n)
        (Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : CoordinateRing n)) H =
      projectiveChartLocalizationMap p *
        algebraMap (CoordinateRing n)
          (Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : CoordinateRing n))
            (MvPolynomial.X 0) ^ k := by
  let X₀ : CoordinateRing n := MvPolynomial.X 0
  let L := Localization.Away X₀
  let J := V.ideal.toIdeal.map (algebraMap (CoordinateRing n) L)
  obtain ⟨s, H, hH⟩ := IsLocalization.exists_integer_multiple'
    (Submonoid.powers X₀) (projectiveChartLocalizationMap p)
  obtain ⟨k, hk⟩ := s.property
  have he : algebraMap (CoordinateRing n) L H =
      projectiveChartLocalizationMap p * algebraMap (CoordinateRing n) L X₀ ^ k := by
    simpa only [← hk, map_pow] using hH
  refine ⟨H, k, ?_, he⟩
  intro hHI
  have hmem : algebraMap (CoordinateRing n) L H ∈ J := Ideal.mem_map_of_mem _ hHI
  rw [he] at hmem
  have hu : IsUnit (algebraMap (CoordinateRing n) L X₀ ^ k) :=
    (IsLocalization.Away.algebraMap_isUnit X₀).pow k
  have hψ : projectiveChartLocalizationMap p ∈ J :=
    (J.mul_unit_mem_iff_mem hu).mp hmem
  have hco := projectiveChartLocalizationMap_comap_ideal V.ideal.toIdeal V.ideal.isHomogeneous
  apply hp
  change p ∈ V.ideal.toIdeal.map affineChartPolynomialMap.toRingHom
  rw [← hco]
  exact hψ

/-- A nonzero polynomial on the integral cone has a nonvanishing actual
complex point; this is the pinned mathlib Nullstellensatz, not an input. -/
theorem projectiveCone_exists_nonvanishing_point
    (V : IntegralProjectiveEquations n) (H : CoordinateRing n)
    (hH : H ∉ V.ideal.toIdeal) :
    ∃ w : CoordinateVector n, w ∈ MvPolynomial.zeroLocus ℂ V.ideal.toIdeal ∧
      MvPolynomial.eval w H ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hm : H ∈ MvPolynomial.vanishingIdeal ℂ
      (MvPolynomial.zeroLocus ℂ V.ideal.toIdeal) := h
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, V.prime.radical] at hm
  exact hH hm

end LinearStudy
