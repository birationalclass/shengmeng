module
public import Linear.ProjectiveConeFinite
public import Linear.ProjectiveAffineVariety
public import Linear.FractionModelAlgebraicOpen
public import Mathlib.RingTheory.Algebraic.Integral
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- A finite ring map to a domain provides an actual nonzero target
element whose pullback is divisible by a chosen nonzero source element. -/
theorem finite_ringHom_exists_nonzero_target_multiple
    {R A : Type*} [CommRing R] [Nontrivial R] [CommRing A] [IsDomain A]
    (φ : R →+* A) (hφ : φ.Finite) (a : A) (ha : a ≠ 0) :
    ∃ b : R, b ≠ 0 ∧ a ∣ φ b := by
  letI : Algebra R A := φ.toAlgebra
  letI : Module.Finite R A := hφ
  exact (Algebra.IsAlgebraic.isAlgebraic (R := R) a).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero ha)

/-- An explicit nonzero target polynomial excludes all source points on
the coordinate hyperplane. The finite-map input is proved for the original f. -/
theorem projectiveConeMap_exists_chart_avoidance_polynomial
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    ∃ H C : CoordinateRing n, H ∉ V.ideal.toIdeal ∧
      (MvPolynomial.aeval f.forms) H - MvPolynomial.X 0 * C ∈ V.ideal.toIdeal := by
  letI := V.prime
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  let π := Ideal.Quotient.mk V.ideal.toIdeal
  have hX : (MvPolynomial.X (0 : Fin (n + 1)) : CoordinateRing n) ∉
      V.ideal.toIdeal := by
    intro h
    have he := ((V.normalizedPoint_mem_iff x).mp hx) _ h
    simpa using he
  have ha : π (MvPolynomial.X 0) ≠ 0 := by
    intro h
    exact hX (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let φ := (projectiveCoordinateDomainMap f V hq hf hV).toRingHom
  obtain ⟨b, hb, c, hc⟩ := finite_ringHom_exists_nonzero_target_multiple
    φ (projectiveCoordinateDomainMap_finite f V hq hf hV) (π (MvPolynomial.X 0)) ha
  obtain ⟨H, hH⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨C, hC⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨H, C, ?_, ?_⟩
  · intro hm
    exact hb (hH.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hm))
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_mul, ← projectiveCoordinateDomainMap_mk f V hq hf hV H, hH, hC]
    exact sub_eq_zero.mpr hc

end LinearStudy
